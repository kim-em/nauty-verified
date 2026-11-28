"""Adds an anonymous [NautyEnv ge] binder to each top-level def/abbrev/structure
that mentions ge but no E.x (after tx.py). `python3 scripts/env/fixdefs.py FILE...`"""
import re,sys
# add an instance binder to top-level defs/structures/abbrevs that mention `ge` but not `E.`
hdr=re.compile(r"^((?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*(?:def|abbrev|structure|inductive|class) )([^\s:(\[{]+)",re.M)
for p in sys.argv[1:]:
    t=open(p).read()
    ms=list(hdr.finditer(t))
    out=t; shift=0
    starts=[m.start() for m in re.finditer(r"^(?=\S)",t,re.M)]
    for m in ms:
        # body: until next line beginning with non-space that starts a decl/comment
        nxt=re.search(r"^(?:theorem|def|abbrev|structure|inductive|class|instance|/--|@\[|end |namespace |section|variable|open |kernel_rfl|macro|elab|set_option|local|attribute|private|protected|noncomputable)",t[m.end():],re.M)
        body=t[m.start(): m.end()+(nxt.start() if nxt else len(t))]
        if re.search(r"\bge\b",body) and "E." not in body and "NautyEnv ge]" not in body:
            ins=m.end()+shift
            out=out[:ins]+" [NautyVerified.Program.NautyEnv ge]"+out[ins:]
            shift+=len(" [NautyVerified.Program.NautyEnv ge]")
            print(p, m.group(2))
    open(p,"w").write(out)
