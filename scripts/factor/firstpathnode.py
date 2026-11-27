# Factoring of nauty.c's `firstpathnode0` for scripts/factor_clight.py.
import importlib.util, os
_s = importlib.util.spec_from_file_location('refine', os.path.join(os.path.dirname(__file__), 'refine.py'))
_r = importlib.util.module_from_spec(_s); _s.loader.exec_module(_r)
MACROS = [mm for mm in _r.MACROS if mm[0] in ('sk', 'tv')]
PIECES = [('tcalloc', 10), ('invstat', 64), ('target', 108), ('leaf', 132), ('cheap', 191),
          ('childLoop', 222), ('child', 232), ('grpsize', 322), ('allsame', 335)]
TOP = 'body'
