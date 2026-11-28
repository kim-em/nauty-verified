import NautyVerified.Source.Dense
import NautyVerified.Source.Nausparse
import NautyVerified.Source.SparseMain

/-! # The sparse harness, linked: `sparse_main.c`, nauty's sparse sources and `zalloc.c`

Numbered extending `dense` (see `c_link`), so the units both programs link
(`nauty.c`, `nautil.c`, `schreier.c`, `naurng.c`, `zalloc.c`) have the same
Clight in both: `sparse.fn.<f> = dense.fn.<f>` for each of their functions
(`Source/Shared.lean`). -/

namespace NautyVerified.Source

c_link sparse := sparse_main nauty nautil nausparse schreier naurng zalloc extending dense

end NautyVerified.Source
