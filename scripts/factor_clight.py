#!/usr/bin/env python3
"""Factor a printed Clight statement into named Lean abbrevs.

Input: the output of `NautyVerified.Tools.stS` (one Lean term) and a spec
module (Python) giving
  MACROS: list of (name, params, body) where body is Lean-term text in the
          printer's syntax that may use earlier macros and `?param` holes;
          occurrences in the term are replaced by `(name arg...)`.
  PIECES: list of (name, line) naming the subterm whose opening parenthesis
          is the first token on that line of the input; each becomes
          `abbrev name : statement := ...`.
  TOP: name of the whole body.
The output is the abbrev block, innermost first; a `kernel_rfl` equality
with the source body (written by hand) checks it.
"""
import importlib.util
import sys

def tokenize(text):
    toks = []
    line = 1
    i = 0
    while i < len(text):
        c = text[i]
        if c == '\n':
            line += 1; i += 1
        elif c.isspace():
            i += 1
        elif c in '()[],':
            toks.append((c, line)); i += 1
        else:
            j = i
            while j < len(text) and not text[j].isspace() and text[j] not in '()[],':
                j += 1
            toks.append((text[i:j], line)); i = j
    return toks

class Node:
    def __init__(self, kind, kids, line):
        self.kind, self.kids, self.line = kind, kids, line  # kind: 'atom' | '(' | '['
    def key(self):
        if self.kind == 'atom':
            return self.kids
        return (self.kind, tuple(k.key() for k in self.kids))

def parse(toks):
    pos = 0
    def go():
        nonlocal pos
        t, ln = toks[pos]
        if t == '(':
            pos += 1
            kids = []
            while toks[pos][0] != ')':
                kids.append(go())
            pos += 1
            return Node('(', kids, ln)
        if t == '[':
            pos += 1
            kids = []
            while toks[pos][0] != ']':
                if toks[pos][0] == ',':
                    pos += 1; continue
                kids.append(go())
            pos += 1
            return Node('[', kids, ln)
        pos += 1
        return Node('atom', t, ln)
    return go()

def atom(s):
    return Node('atom', s, 0)

def show(n):
    if n.kind == 'atom':
        return n.kids
    if n.kind == '[':
        return '[' + ', '.join(show(k) for k in n.kids) + ']'
    return '(' + ' '.join(show(k) for k in n.kids) + ')'

def pretty(n, ind, width=100):
    flat = show(n)
    if len(flat) + ind <= width or n.kind == 'atom':
        return flat
    if n.kind == '[':
        return '[' + (',\n' + ' ' * (ind + 1)).join(pretty(k, ind + 1, width) for k in n.kids) + ']'
    head = []
    rest = list(n.kids)
    while rest and rest[0].kind == 'atom':
        head.append(rest.pop(0).kids)
    s = '(' + ' '.join(head)
    for k in rest:
        s += '\n' + ' ' * (ind + 2) + pretty(k, ind + 2, width)
    return s + ')'

def match(pat, n, env):
    if pat.kind == 'atom' and pat.kids.startswith('?'):
        h = pat.kids
        if h in env:
            return env[h].key() == n.key()
        env[h] = n
        return True
    if pat.kind != n.kind:
        return False
    if pat.kind == 'atom':
        return pat.kids == n.kids
    if len(pat.kids) != len(n.kids):
        return False
    return all(match(p, k, env) for p, k in zip(pat.kids, n.kids))

def subst(tmpl, env):
    if tmpl.kind == 'atom':
        return env.get(tmpl.kids, tmpl)
    return Node(tmpl.kind, [subst(k, env) for k in tmpl.kids], 0)

def main():
    spec_path, term_path = sys.argv[1], sys.argv[2]
    spec = importlib.util.spec_from_file_location('spec', spec_path)
    S = importlib.util.module_from_spec(spec); spec.loader.exec_module(S)
    tree = parse(tokenize(open(term_path).read()))
    # expand macro bodies to raw trees, in order (later macros may use earlier)
    raw = {}
    pats = []
    for name, params, body in S.MACROS:
        t = parse(tokenize(body))
        def expand(t):
            if t.kind == '(' and t.kids and t.kids[0].kind == 'atom' and t.kids[0].kids in raw:
                ps, b = raw[t.kids[0].kids]
                args = [expand(k) for k in t.kids[1:]]
                return subst(b, dict(zip(ps, args)))
            if t.kind == 'atom':
                return t
            return Node(t.kind, [expand(k) for k in t.kids], t.line)
        t = expand(t)
        raw[name] = (['?' + p for p in params], t)
        pats.append((name, ['?' + p for p in params], t))
    pats.reverse()  # later (larger) macros are tried first
    pieces = {ln: name for name, ln in S.PIECES}
    out = []
    def rewrite(n, top=False):
        if not top and n.kind == '(' and n.line in pieces and n.kids and n.kids[0].kind == 'atom' \
                and n.kids[0].kids.startswith('.S'):
            name = pieces.pop(n.line)
            body = rewrite(n, top=True)
            out.append((name, body))
            return atom(name)
        if n.kind == 'atom':
            return n
        for name, ps, p in pats:
            env = {}
            if match(p, n, env):
                return Node('(', [atom(name)] + [rewrite(env[h]) for h in ps], 0)
        return Node(n.kind, [rewrite(k) for k in n.kids], n.line)
    body = rewrite(tree, top=True)
    out.append((S.TOP, body))
    if pieces:
        print('unused pieces:', pieces, file=sys.stderr)
    for name, b in out:
        print(f'abbrev {name} : statement :=\n  ' + pretty(b, 2) + '\n')

if __name__ == '__main__':
    main()
