import NautyVerified.Source.Sparse

/-! # The functions the dense and the sparse program share

Every function of `nauty.c`, `nautil.c`, `schreier.c`, `naurng.c` and
`zalloc.c` has the same Clight in the linked sparse program as in the linked
dense program (`sparse` is numbered extending `dense`, see `c_link`), each
equation checked by the kernel. Proofs about these functions in the dense
program therefore describe the sparse program's functions too, once they are
stated over a global environment in which the callees sit where the sparse
program puts them (docs/PLAN.md, Phase 7). -/

namespace NautyVerified.Source.sparse.fn

kernel_rfl addgenerator_eq : addgenerator = dense.fn.addgenerator
kernel_rfl addpermutation_eq : addpermutation = dense.fn.addpermutation
kernel_rfl alloc_error_eq : alloc_error = dense.fn.alloc_error
kernel_rfl breakout_eq : breakout = dense.fn.breakout
kernel_rfl condaddgenerator_eq : condaddgenerator = dense.fn.condaddgenerator
kernel_rfl deleteunmarked_eq : deleteunmarked = dense.fn.deleteunmarked
kernel_rfl doref_eq : doref = dense.fn.doref
kernel_rfl dumpschreier_eq : dumpschreier = dense.fn.dumpschreier
kernel_rfl expandschreier_eq : expandschreier = dense.fn.expandschreier
kernel_rfl extra_autom_eq : extra_autom = dense.fn.extra_autom
kernel_rfl extra_level_eq : extra_level = dense.fn.extra_level
kernel_rfl findpermutation_eq : findpermutation = dense.fn.findpermutation
kernel_rfl fmperm_eq : fmperm = dense.fn.fmperm
kernel_rfl fmptn_eq : fmptn = dense.fn.fmptn
kernel_rfl freeschreier_eq : freeschreier = dense.fn.freeschreier
kernel_rfl getorbits_eq : getorbits = dense.fn.getorbits
kernel_rfl getorbitsmin_eq : getorbitsmin = dense.fn.getorbitsmin
kernel_rfl grouporder_eq : grouporder = dense.fn.grouporder
kernel_rfl itos_eq : itos = dense.fn.itos
kernel_rfl longprune_eq : longprune = dense.fn.longprune
kernel_rfl maketargetcell_eq : maketargetcell = dense.fn.maketargetcell
kernel_rfl «nautil:sortparallel_eq» : «nautil:sortparallel» = dense.fn.«nautil:sortparallel»
kernel_rfl nautil_check_eq : nautil_check = dense.fn.nautil_check
kernel_rfl nautil_freedyn_eq : nautil_freedyn = dense.fn.nautil_freedyn
kernel_rfl nauty_eq : nauty = dense.fn.nauty
kernel_rfl «nauty:firstpathnode0_eq» : «nauty:firstpathnode0» = dense.fn.«nauty:firstpathnode0»
kernel_rfl «nauty:firstterminal_eq» : «nauty:firstterminal» = dense.fn.«nauty:firstterminal»
kernel_rfl «nauty:othernode0_eq» : «nauty:othernode0» = dense.fn.«nauty:othernode0»
kernel_rfl «nauty:processnode_eq» : «nauty:processnode» = dense.fn.«nauty:processnode»
kernel_rfl «nauty:recover_eq» : «nauty:recover» = dense.fn.«nauty:recover»
kernel_rfl «nauty:writemarker_eq» : «nauty:writemarker» = dense.fn.«nauty:writemarker»
kernel_rfl nauty_check_eq : nauty_check = dense.fn.nauty_check
kernel_rfl nauty_freedyn_eq : nauty_freedyn = dense.fn.nauty_freedyn
kernel_rfl nauty_zalloc_eq : nauty_zalloc = dense.fn.nauty_zalloc
kernel_rfl newgroup_eq : newgroup = dense.fn.newgroup
kernel_rfl nextelement_eq : nextelement = dense.fn.nextelement
kernel_rfl orbjoin_eq : orbjoin = dense.fn.orbjoin
kernel_rfl permset_eq : permset = dense.fn.permset
kernel_rfl pruneset_eq : pruneset = dense.fn.pruneset
kernel_rfl putstring_eq : putstring = dense.fn.putstring
kernel_rfl ran_init_eq : ran_init = dense.fn.ran_init
kernel_rfl ran_init_2_eq : ran_init_2 = dense.fn.ran_init_2
kernel_rfl ran_init_time_eq : ran_init_time = dense.fn.ran_init_time
kernel_rfl ran_nextran_eq : ran_nextran = dense.fn.ran_nextran
kernel_rfl «schreier:addpermutationunmarked_eq» : «schreier:addpermutationunmarked» = dense.fn.«schreier:addpermutationunmarked»
kernel_rfl «schreier:applyperm_eq» : «schreier:applyperm» = dense.fn.«schreier:applyperm»
kernel_rfl «schreier:clearfreelists_eq» : «schreier:clearfreelists» = dense.fn.«schreier:clearfreelists»
kernel_rfl «schreier:clearvector_eq» : «schreier:clearvector» = dense.fn.«schreier:clearvector»
kernel_rfl «schreier:delpermnode_eq» : «schreier:delpermnode» = dense.fn.«schreier:delpermnode»
kernel_rfl «schreier:filterschreier_eq» : «schreier:filterschreier» = dense.fn.«schreier:filterschreier»
kernel_rfl «schreier:initschreier_eq» : «schreier:initschreier» = dense.fn.«schreier:initschreier»
kernel_rfl «schreier:newpermnode_eq» : «schreier:newpermnode» = dense.fn.«schreier:newpermnode»
kernel_rfl «schreier:newschreier_eq» : «schreier:newschreier» = dense.fn.«schreier:newschreier»
kernel_rfl schreier_check_eq : schreier_check = dense.fn.schreier_check
kernel_rfl schreier_fails_eq : schreier_fails = dense.fn.schreier_fails
kernel_rfl schreier_freedyn_eq : schreier_freedyn = dense.fn.schreier_freedyn
kernel_rfl schreier_gens_eq : schreier_gens = dense.fn.schreier_gens
kernel_rfl shortprune_eq : shortprune = dense.fn.shortprune
kernel_rfl writegroupsize_eq : writegroupsize = dense.fn.writegroupsize
kernel_rfl writeperm_eq : writeperm = dense.fn.writeperm

-- `cheapautom_sg` (nausparse.c) has the same source as naugraph.c's
-- `cheapautom`, and the same Clight.
kernel_rfl cheapautom_sg_eq : cheapautom_sg = dense.fn.cheapautom

end NautyVerified.Source.sparse.fn
