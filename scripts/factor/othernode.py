# Factoring of nauty.c's `othernode0` for scripts/factor_clight.py.
import importlib.util, os
_s = importlib.util.spec_from_file_location('refine', os.path.join(os.path.dirname(__file__), 'refine.py'))
_r = importlib.util.module_from_spec(_s); _s.loader.exec_module(_r)
MACROS = [mm for mm in _r.MACROS if mm[0] in ('sk', 'tv')]
PIECES = [('tcalloc', 10), ('kill', 54), ('invstat', 74), ('codeFirst', 99), ('codeCanon', 112),
          ('target', 153), ('prune0', 230), ('cheap', 244), ('childLoop', 260)]
TOP = 'body'
