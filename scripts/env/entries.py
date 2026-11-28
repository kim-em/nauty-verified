"""The NautyEnv fields: (field, origin namespace P/S/T, dense.id key, kind, function).

kind is var, fn, malloc or free. The S entries are read from
Proofs/Search/Blocks.lean, skipping the naugraph.c dispatch blocks. Imported by
genenv.py and gensparse.py; run directly it prints the number of fields.
"""
import os
ROOT=os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)),"..",".."))
import re
# (field, origin namespace ("P","S","T"), key, kind, fn)
# kind: var | fn | malloc | free
E=[]
def add(f,ns,key,kind,fn=None): E.append((f,ns,key,kind,fn))
add("nextelement","P","nextelement","fn","nextelement")
add("leftbit","P","«nautil:leftbit»","var")
add("nautilBit","P","«nautil:bit»","var")
add("malloc","P","malloc","malloc")
add("free","P","free","free")
add("zalloc","P","nauty_zalloc","fn","nauty_zalloc")
add("nautilWorkperm","P","«nautil:workperm»","var")
add("nautilWorkpermSz","P","«nautil:workperm_sz»","var")
add("permset","P","permset","fn","permset")
add("nautyBit","P","«nauty:bit»","var")
for nm,c in [("Canonlab","canonlab"),("Defltwork","defltwork"),("Active","active"),("Canoncode","canoncode"),("Fixedpts","fixedpts"),("Firstcode","firstcode"),("Workperm","workperm"),("Firsttc","firsttc"),("Firstlab","firstlab")]:
    add("nauty"+nm,"P","«nauty:%s»"%c,"var")
    add("nauty"+nm+"Sz","P","«nauty:%s_sz»"%c,"var")
t=open(os.path.join(ROOT,"NautyVerified/Proofs/Search/Blocks.lean")).read()
skip={"densenautyFn","isautomFn","testcanlabFn","updatecanFn","cheapautomFn","targetcellFn","dispatchGraph","permsetFn"}
fns={"firstpathnodeFn":"«nauty:firstpathnode0»","othernodeFn":"«nauty:othernode0»","firstterminalFn":"«nauty:firstterminal»","processnodeFn":"«nauty:processnode»","recoverFn":"«nauty:recover»","nautyFn":"«nauty»","maketargetcellFn":"«maketargetcell»","breakoutFn":"«breakout»","fmpermFn":"«fmperm»","fmptnFn":"«fmptn»","orbjoinFn":"«orbjoin»","shortpruneFn":"«shortprune»","longpruneFn":"«longprune»","dorefFn":"«doref»"}
for m in re.finditer(r"kernel_rfl find_(\w+) : Genv.find_symbol ge.genv_genv dense.id.(\S+) = some Block.(\w+)",t):
    f,k=m.group(1),m.group(2)
    if f in skip: continue
    if f in fns: add(f,"S",k,"fn",fns[f])
    else: add(f,"S",k,"var")
add("nautilCheck","T","nautil_check","fn","nautil_check")
add("nautilFreedyn","T","nautil_freedyn","fn","nautil_freedyn")
add("nautyFreedyn","T","nauty_freedyn","fn","nauty_freedyn")
ENTRIES=E
if __name__=="__main__": print(len(E))
