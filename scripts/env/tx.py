"""Rewrites Lean files to take [E : NautyEnv ge]: Block.x, find_x, funct_x for a
NautyEnv field x become E.x, E.find_x, E.funct_x; adds the variable line after
the first namespace and the Program.Env import. `python3 scripts/env/tx.py FILE...`"""
import sys; import os; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from entries import ENTRIES
import re,sys,json
E=ENTRIES
names=set(f for f,*_ in E)|{"permsetFn"}
alt="|".join(sorted(names,key=len,reverse=True))
for p in sys.argv[1:]:
    t=open(p).read()
    o=t
    t=re.sub(r"(?<![\w.])(?:NautyVerified\.)?(?:Proofs\.)?(?:Program\.|Search\.|Top\.)?Block\.(%s)\b"%alt, r"E.\1", t)
    t=re.sub(r"(?<![\w.])(?:NautyVerified\.)?(?:Proofs\.)?(?:Program\.|Search\.|Top\.)?(find|funct)_(%s)\b"%alt, r"E.\1_\2", t)
    if "[E : NautyVerified.Program.NautyEnv ge]" not in t:
        lines=t.split("\n")
        for i,l in enumerate(lines):
            if l.startswith("namespace "):
                lines.insert(i+1,"\nvariable {ge : CompCert4Lean.Cfrontend.Clight.genv} [E : NautyVerified.Program.NautyEnv ge]\nset_option linter.unusedSectionVars false")
                break
        t="\n".join(lines)
    if "import NautyVerified.Program.Env\n" not in t:
        t="import NautyVerified.Program.Env\n"+t
    open(p,"w").write(t)
    print(p, "changed" if t!=o else "same")
