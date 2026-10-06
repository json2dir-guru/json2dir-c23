// json2dir: create the directory tree a JSON document describes, in the current directory.
// Implements RFC J2D-1 (https://github.com/kitsunoff/awesome-json2dir/blob/main/spec/rfc-json2dir.md).
// C23 (ISO/IEC 9899:2024) + POSIX.1-2008, one file, hand-written UTF-8 check and JSON parser.
#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <stdarg.h>
#include <fcntl.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

#if __STDC_VERSION__ < 202311L
#error "json2dir.c needs a C23 compiler (-std=c23)"
#endif

constexpr int max_depth = 1'000;          // nesting limit of the parser (the spec asks for >= 64)
constexpr size_t read_chunk = 64 * 1'024;

static_assert(max_depth >= 64);
static_assert(sizeof(char) == 1);

enum kind : unsigned char { K_STRING, K_OBJECT, K_ARRAY, K_SCALAR };

typedef struct node node;
typedef struct member member;

struct node {
    enum kind kind;
    char *str;        // K_STRING: decoded bytes, NUL-terminated (may also contain NULs)
    size_t len;
    member *members;  // K_OBJECT
    node *items;      // K_ARRAY
    size_t count;     // number of members / items
};

struct member {
    node name;        // always a K_STRING
    node value;
    size_t index;     // position in the document, for "last duplicate wins"
};

// ---------------------------------------------------------------- diagnostics

[[noreturn]] static void die(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    fputs("json2dir: ", stderr);
    vfprintf(stderr, fmt, ap);
    fputc('\n', stderr);
    va_end(ap);
    exit(1);
}

[[nodiscard]] static void *xrealloc(void *p, size_t n) {
    void *q = realloc(p, n ? n : 1);
    if (q == nullptr) die("out of memory");
    return q;
}

// ---------------------------------------------------------------- input

[[nodiscard]] static unsigned char *read_all(int fd, size_t *out_len) {
    unsigned char *buf = nullptr;
    size_t len = 0, cap = 0;
    for (;;) {
        if (cap - len < read_chunk) {
            cap = cap * 2 + read_chunk;
            buf = xrealloc(buf, cap + 1);
        }
        auto n = read(fd, buf + len, cap - len);
        if (n < 0) {
            if (errno == EINTR) continue;
            die("cannot read standard input: %s", strerror(errno));
        }
        if (n == 0) break;
        len += (size_t)n;
    }
    buf[len] = 0;
    *out_len = len;
    return buf;
}

// §3: strict UTF-8 (no overlongs, no surrogates, nothing above U+10FFFF).
[[nodiscard]] static bool valid_utf8(const unsigned char *s, size_t n) {
    size_t i = 0;
    while (i < n) {
        unsigned char c = s[i];
        if (c < 0x80) { i++; continue; }
        size_t need;
        unsigned char lo = 0x80, hi = 0xBF;
        if ((c & 0b1110'0000) == 0b1100'0000) {
            if (c < 0xC2) return false;
            need = 1;
        } else if ((c & 0b1111'0000) == 0b1110'0000) {
            need = 2;
            if (c == 0xE0) lo = 0xA0;
            if (c == 0xED) hi = 0x9F;
        } else if ((c & 0b1111'1000) == 0b1111'0000) {
            if (c > 0xF4) return false;
            need = 3;
            if (c == 0xF0) lo = 0x90;
            if (c == 0xF4) hi = 0x8F;
        } else {
            return false;
        }
        if (n - i - 1 < need) return false;
        for (size_t k = 1; k <= need; k++) {
            unsigned char b = s[i + k];
            if (k == 1 ? (b < lo || b > hi) : (b & 0b1100'0000) != 0b1000'0000) return false;
        }
        i += need + 1;
    }
    return true;
}

// ---------------------------------------------------------------- JSON parser

typedef struct {
    const unsigned char *p, *end;
} parser;

static void skip_ws(parser *ps) {
    while (ps->p < ps->end && (*ps->p == ' ' || *ps->p == '\t' || *ps->p == '\n' || *ps->p == '\r'))
        ps->p++;
}

[[noreturn]] static void syntax(const parser *ps, const char *what) {
    die("input is not valid JSON: %s", ps->p < ps->end ? what : "unexpected end of input");
}

static void put_byte(node *s, size_t *cap, unsigned char b) {
    if (s->len + 1 >= *cap) {
        *cap = *cap * 2 + 16;
        s->str = xrealloc(s->str, *cap);
    }
    s->str[s->len++] = (char)b;
}

static void put_utf8(node *s, size_t *cap, uint32_t cp) {
    if (cp < 0x80) {
        put_byte(s, cap, (unsigned char)cp);
    } else if (cp < 0x800) {
        put_byte(s, cap, (unsigned char)(0xC0 | cp >> 6));
        put_byte(s, cap, (unsigned char)(0x80 | (cp & 0x3F)));
    } else if (cp < 0x1'0000) {
        put_byte(s, cap, (unsigned char)(0xE0 | cp >> 12));
        put_byte(s, cap, (unsigned char)(0x80 | (cp >> 6 & 0x3F)));
        put_byte(s, cap, (unsigned char)(0x80 | (cp & 0x3F)));
    } else {
        put_byte(s, cap, (unsigned char)(0xF0 | cp >> 18));
        put_byte(s, cap, (unsigned char)(0x80 | (cp >> 12 & 0x3F)));
        put_byte(s, cap, (unsigned char)(0x80 | (cp >> 6 & 0x3F)));
        put_byte(s, cap, (unsigned char)(0x80 | (cp & 0x3F)));
    }
}

[[nodiscard]] static uint32_t hex4(parser *ps) {
    if (ps->end - ps->p < 4) syntax(ps, "truncated \\u escape");
    uint32_t v = 0;
    for (int i = 0; i < 4; i++) {
        unsigned char c = *ps->p++;
        v <<= 4;
        if (c >= '0' && c <= '9') v |= c - '0';
        else if (c >= 'a' && c <= 'f') v |= c - 'a' + 10;
        else if (c >= 'A' && c <= 'F') v |= c - 'A' + 10;
        else syntax(ps, "bad \\u escape");
    }
    return v;
}

// Called with ps->p just after the opening quote. Input is already known to be valid UTF-8.
[[nodiscard]] static node parse_string(parser *ps) {
    node s = {};
    s.kind = K_STRING;
    size_t cap = 0;
    put_byte(&s, &cap, 0);
    s.len = 0;
    for (;;) {
        if (ps->p >= ps->end) syntax(ps, "unterminated string");
        unsigned char c = *ps->p++;
        if (c == '"') break;
        if (c < 0x20) syntax(ps, "control character in string");
        if (c != '\\') { put_byte(&s, &cap, c); continue; }
        if (ps->p >= ps->end) syntax(ps, "unterminated string");
        unsigned char e = *ps->p++;
        switch (e) {
        case '"': case '\\': case '/': put_byte(&s, &cap, e); break;
        case 'b': put_byte(&s, &cap, '\b'); break;
        case 'f': put_byte(&s, &cap, '\f'); break;
        case 'n': put_byte(&s, &cap, '\n'); break;
        case 'r': put_byte(&s, &cap, '\r'); break;
        case 't': put_byte(&s, &cap, '\t'); break;
        case 'u': {
            uint32_t cp = hex4(ps);
            if (cp >= 0xD800 && cp <= 0xDBFF) {
                if (ps->end - ps->p < 2 || ps->p[0] != '\\' || ps->p[1] != 'u')
                    die("input contains an unpaired surrogate escape");
                ps->p += 2;
                uint32_t lo = hex4(ps);
                if (lo < 0xDC00 || lo > 0xDFFF) die("input contains an unpaired surrogate escape");
                cp = 0x1'0000 + ((cp - 0xD800) << 10) + (lo - 0xDC00);
            } else if (cp >= 0xDC00 && cp <= 0xDFFF) {
                die("input contains an unpaired surrogate escape");
            }
            put_utf8(&s, &cap, cp);
            break;
        }
        default: syntax(ps, "bad escape in string");
        }
    }
    s.str[s.len] = 0;
    return s;
}

static bool is_digit(unsigned char c) { return c >= '0' && c <= '9'; }

// Numbers are parsed by the JSON grammar only to be rejected later (§4.5).
static void parse_number(parser *ps) {
    if (ps->p < ps->end && *ps->p == '-') ps->p++;
    if (ps->p >= ps->end || !is_digit(*ps->p)) syntax(ps, "bad number");
    if (*ps->p == '0') ps->p++;
    else while (ps->p < ps->end && is_digit(*ps->p)) ps->p++;
    if (ps->p < ps->end && *ps->p == '.') {
        ps->p++;
        if (ps->p >= ps->end || !is_digit(*ps->p)) syntax(ps, "bad number");
        while (ps->p < ps->end && is_digit(*ps->p)) ps->p++;
    }
    if (ps->p < ps->end && (*ps->p == 'e' || *ps->p == 'E')) {
        ps->p++;
        if (ps->p < ps->end && (*ps->p == '+' || *ps->p == '-')) ps->p++;
        if (ps->p >= ps->end || !is_digit(*ps->p)) syntax(ps, "bad number");
        while (ps->p < ps->end && is_digit(*ps->p)) ps->p++;
    }
}

[[nodiscard]] static node parse_value(parser *ps, int depth) {
    if (depth > max_depth) die("input is nested too deeply");
    skip_ws(ps);
    if (ps->p >= ps->end) syntax(ps, "");
    node v = {};
    unsigned char c = *ps->p;
    if (c == '"') {
        ps->p++;
        return parse_string(ps);
    }
    if (c == '{') {
        ps->p++;
        v.kind = K_OBJECT;
        size_t cap = 0;
        skip_ws(ps);
        if (ps->p < ps->end && *ps->p == '}') { ps->p++; return v; }
        for (;;) {
            skip_ws(ps);
            if (ps->p >= ps->end || *ps->p != '"') syntax(ps, "expected a member name");
            ps->p++;
            if (v.count == cap) {
                cap = cap * 2 + 4;
                v.members = xrealloc(v.members, cap * sizeof *v.members);
            }
            typeof(v.members) m = &v.members[v.count];
            m->index = v.count++;
            m->name = parse_string(ps);
            skip_ws(ps);
            if (ps->p >= ps->end || *ps->p != ':') syntax(ps, "expected ':'");
            ps->p++;
            m->value = parse_value(ps, depth + 1);
            skip_ws(ps);
            if (ps->p < ps->end && *ps->p == ',') { ps->p++; continue; }
            if (ps->p < ps->end && *ps->p == '}') { ps->p++; return v; }
            syntax(ps, "expected ',' or '}'");
        }
    }
    if (c == '[') {
        ps->p++;
        v.kind = K_ARRAY;
        size_t cap = 0;
        skip_ws(ps);
        if (ps->p < ps->end && *ps->p == ']') { ps->p++; return v; }
        for (;;) {
            auto item = parse_value(ps, depth + 1);
            if (v.count == cap) {
                cap = cap * 2 + 2;
                v.items = xrealloc(v.items, cap * sizeof *v.items);
            }
            v.items[v.count++] = item;
            skip_ws(ps);
            if (ps->p < ps->end && *ps->p == ',') { ps->p++; continue; }
            if (ps->p < ps->end && *ps->p == ']') { ps->p++; return v; }
            syntax(ps, "expected ',' or ']'");
        }
    }
    v.kind = K_SCALAR;
    static const char *const literals[] = {"true", "false", "null"};
    for (size_t i = 0; i < sizeof literals / sizeof literals[0]; i++) {
        size_t n = strlen(literals[i]);
        if ((size_t)(ps->end - ps->p) >= n && memcmp(ps->p, literals[i], n) == 0) {
            ps->p += n;
            return v;
        }
    }
    if (c == '-' || is_digit(c)) {
        parse_number(ps);
        return v;
    }
    syntax(ps, "unexpected character");
}

// ---------------------------------------------------------------- validation (§4)

static int by_name(const void *a, const void *b) {
    const member *x = a, *y = b;
    size_t n = x->name.len < y->name.len ? x->name.len : y->name.len;
    int c = memcmp(x->name.str, y->name.str, n);
    if (c != 0) return c;
    if (x->name.len != y->name.len) return x->name.len < y->name.len ? -1 : 1;
    return x->index < y->index ? -1 : x->index > y->index;
}

// Sorts members by the UTF-8 bytes of their names and keeps only the last of duplicates.
static void sort_members(node *obj) {
    if (obj->count == 0) return;
    qsort(obj->members, obj->count, sizeof obj->members[0], by_name);
    size_t out = 0;
    for (size_t i = 0; i < obj->count; i++) {
        auto m = &obj->members[i];
        bool dup_follows = i + 1 < obj->count && m->name.len == m[1].name.len &&
                           memcmp(m->name.str, m[1].name.str, m->name.len) == 0;
        if (!dup_follows) obj->members[out++] = *m;
    }
    obj->count = out;
}

static bool valid_name(const node *name) {
    if (name->len == 0) return false;
    if (name->len == 1 && name->str[0] == '.') return false;
    if (name->len == 2 && name->str[0] == '.' && name->str[1] == '.') return false;
    return memchr(name->str, '/', name->len) == nullptr && memchr(name->str, 0, name->len) == nullptr;
}

static void validate(node *obj, const char *where) {
    sort_members(obj);
    for (size_t i = 0; i < obj->count; i++) {
        auto m = &obj->members[i];
        if (!valid_name(&m->name)) die("%s: invalid name \"%s\"", where, m->name.str);
        const node *v = &m->value;
        switch (v->kind) {
        case K_STRING:
            break;
        case K_OBJECT:
            validate(&m->value, m->name.str);
            break;
        case K_ARRAY:
            if (v->count != 2 || v->items[0].kind != K_STRING || v->items[1].kind != K_STRING)
                die("%s: an array must be [\"link\", target] or [\"script\", content]", m->name.str);
            if (strcmp(v->items[0].str, "link") == 0 && v->items[0].len == 4) {
                if (memchr(v->items[1].str, 0, v->items[1].len) != nullptr)
                    die("%s: a link target cannot contain NUL", m->name.str);
                if (v->items[1].len == 0) die("%s: a link target cannot be empty", m->name.str);
            } else if (!(strcmp(v->items[0].str, "script") == 0 && v->items[0].len == 6)) {
                die("%s: unknown array kind", m->name.str);
            }
            break;
        case K_SCALAR:
            die("%s: numbers, booleans and null are not allowed", m->name.str);
        default:
            unreachable();
        }
    }
}

// ---------------------------------------------------------------- file system (§5)

static void write_file(int dirfd, const char *name, const node *content, bool executable) {
    // O_EXCL | O_NOFOLLOW: never write through an entry that appeared after it was removed.
    int fd = openat(dirfd, name, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW, 0666);
    if (fd < 0) die("%s: cannot create file: %s", name, strerror(errno));
    size_t done = 0;
    while (done < content->len) {
        auto n = write(fd, content->str + done, content->len - done);
        if (n < 0) {
            if (errno == EINTR) continue;
            die("%s: cannot write: %s", name, strerror(errno));
        }
        done += (size_t)n;
    }
    if (executable) {
        struct stat st = {};
        if (fstat(fd, &st) != 0 || fchmod(fd, (st.st_mode & 07777) | 0111) != 0)
            die("%s: cannot make executable: %s", name, strerror(errno));
    }
    if (close(fd) != 0) die("%s: cannot close: %s", name, strerror(errno));
}

static void apply(int dirfd, const node *obj) {
    for (size_t i = 0; i < obj->count; i++) {
        typeof_unqual(obj->members[0]) const *m = &obj->members[i];
        const char *name = m->name.str;
        const node *v = &m->value;
        struct stat st = {};
        bool exists = true;
        if (fstatat(dirfd, name, &st, AT_SYMLINK_NOFOLLOW) != 0) {
            if (errno != ENOENT) die("%s: %s", name, strerror(errno));
            exists = false;
        }
        bool is_dir = exists && S_ISDIR(st.st_mode);
        if (v->kind == K_OBJECT) {
            if (!is_dir) {
                if (exists && unlinkat(dirfd, name, 0) != 0) die("%s: cannot remove: %s", name, strerror(errno));
                if (mkdirat(dirfd, name, 0777) != 0) die("%s: cannot create directory: %s", name, strerror(errno));
            }
            int sub = openat(dirfd, name, O_RDONLY | O_DIRECTORY | O_NOFOLLOW);
            if (sub < 0) die("%s: cannot open directory: %s", name, strerror(errno));
            apply(sub, v);
            close(sub);
            continue;
        }
        if (is_dir) die("%s: a directory is in the way", name);
        if (exists && unlinkat(dirfd, name, 0) != 0) die("%s: cannot remove: %s", name, strerror(errno));
        if (v->kind == K_STRING) {
            write_file(dirfd, name, v, false);
        } else if (v->items[0].len == 4) {  // "link" (validated)
            if (symlinkat(v->items[1].str, dirfd, name) != 0)
                die("%s: cannot create symlink: %s", name, strerror(errno));
        } else {                            // "script"
            write_file(dirfd, name, &v->items[1], true);
        }
    }
}

// ---------------------------------------------------------------- main

int main(int argc, [[maybe_unused]] char **argv) {
    if (argc > 1) {
        fputs("usage: json2dir < document.json\n", stderr);
        return 2;
    }
    size_t len = 0;
    unsigned char *buf = read_all(STDIN_FILENO, &len);
    const unsigned char *start = buf;
    if (len >= 3 && buf[0] == 0xEF && buf[1] == 0xBB && buf[2] == 0xBF) start += 3;  // optional BOM
    if (!valid_utf8(start, len - (size_t)(start - buf))) die("input is not valid UTF-8");

    parser ps = {.p = start, .end = buf + len};
    auto doc = parse_value(&ps, 0);
    skip_ws(&ps);
    if (ps.p != ps.end) die("input is not valid JSON: trailing data after the value");
    if (doc.kind != K_OBJECT) die("the root of the document must be an object");

    validate(&doc, ".");
    apply(AT_FDCWD, &doc);
    return 0;
}
