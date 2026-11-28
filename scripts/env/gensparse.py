"""Writes NautyVerified/Program/Sparse.lean (sparseGe, NautyEnv.sparse) from
entries.py and the sparse program's blocks:

    lake env lean scripts/env/blocks.lean > /tmp/blocks.txt
    python3 scripts/env/gensparse.py /tmp/blocks.txt
"""
import os
ROOT=os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)),"..",".."))
import sys; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from entries import ENTRIES
E=ENTRIES
B={}
for l in open(sys.argv[1]):
    import re
    m=re.match(r"(\S+) (\d+) (none|\(some \d+\)) (none|\(some (\d+)\))",l)
    if m and m.group(1) not in B: B[m.group(1)]=m.group(5)
NS={"P":"Block","S":"Search.Block","T":"Top.Block"}
def funct(kind,fn):
    if kind=="fn": return "some (.Internal dense.fn.%s)"%fn
    if kind=="malloc": return "some (.External .EF_malloc [tulong] (tptr .Tvoid) Common.AST.cc_default)"
    if kind=="free": return "some (.External .EF_free [tptr .Tvoid] .Tvoid Common.AST.cc_default)"
o=[]; w=o.append
w("""import NautyVerified.Program.Env
import NautyVerified.Source.Shared

/-!
# The linked sparse program's global environment

`sparseGe`, the global environment of `sparse.locals`, the blocks the sparse
program gives the globals of `NautyEnv`, and `NautyEnv.sparse`, each fact
checked by the kernel. The functions at these blocks are `dense.fn.*`, the
sparse program's Clight being the dense program's (`Source/Shared.lean`).

`NautyEnv.sparse` is not a global instance (the environment is an `outParam`,
so two global instances would compete); proofs about the sparse program
activate it with `attribute [local instance] NautyEnv.sparse`.
-/

namespace NautyVerified.Program

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Foundation.Numbers.Rocq.Coq
open NautyVerified.Source NautyVerified.Proofs

/-- The global environment of the linked sparse program. -/
abbrev sparseGe : genv := globalenv sparse.locals

namespace SparseBlock""")
for f,ns,k,kind,fn in E:
    n=B[k.strip("«»")]
    w("def %s : block := PArith.BinPos.Pos.of_nat %s"%(f,n))
w("end SparseBlock\n\nnamespace SparseEnv\n")
for f,ns,k,kind,fn in E:
    w("kernel_rfl find_%s :\n  Genv.find_symbol sparseGe.genv_genv dense.id.%s = some SparseBlock.%s"%(f,k,f))
for f,ns,k,kind,fn in E:
    if kind!="var":
        w("kernel_rfl funct_%s :\n  Genv.find_funct_ptr sparseGe.genv_genv SparseBlock.%s = %s"%(f,f,funct(kind,fn)))
for f,ns,k,kind,fn in E:
    if kind=="var":
        w("kernel_rfl var_%s : Genv.find_var_info sparseGe.genv_genv SparseBlock.%s =\n  Genv.find_var_info ge.genv_genv %s.%s"%(f,f,NS[ns],f))
w("kernel_rfl distinct : decide (List.Pairwise (· ≠ ·)\n    [%s]) = true"%", ".join("SparseBlock."+f for f,*_ in E))
w("\nend SparseEnv\n\n/-- The sparse program's blocks. -/\n@[reducible] def NautyEnv.sparse : NautyEnv sparseGe where")
for f,*_ in E: w("  %s := SparseBlock.%s"%(f,f))
for f,*_ in E: w("  find_%s := SparseEnv.find_%s"%(f,f))
for f,ns,k,kind,fn in E:
    if kind!="var": w("  funct_%s := SparseEnv.funct_%s"%(f,f))
for f,ns,k,kind,fn in E:
    if kind=="var": w("  var_%s := SparseEnv.var_%s"%(f,f))
w("  distinct := of_decide_eq_true SparseEnv.distinct\n\nend NautyVerified.Program")
open(os.path.join(ROOT,"NautyVerified/Program/Sparse.lean"),"w").write("\n".join(o)+"\n")
