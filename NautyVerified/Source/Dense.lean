import NautyVerified.Source.Link
import NautyVerified.Source.Nauty
import NautyVerified.Source.Nautil
import NautyVerified.Source.Naugraph
import NautyVerified.Source.Schreier
import NautyVerified.Source.Naurng
import NautyVerified.Source.DenseMain
import NautyVerified.Source.Zalloc

/-! # The dense harness, linked: `dense_main.c`, nauty's dense sources and `zalloc.c` -/

namespace NautyVerified.Source

c_link dense := dense_main nauty nautil naugraph schreier naurng zalloc

end NautyVerified.Source
