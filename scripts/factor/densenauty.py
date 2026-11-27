# Factoring of naugraph.c's `densenauty` for scripts/factor_clight.py.
import importlib.util, os
_s = importlib.util.spec_from_file_location('refine', os.path.join(os.path.dirname(__file__), 'refine.py'))
_r = importlib.util.module_from_spec(_s); _s.loader.exec_module(_r)
MACROS = [mm for mm in _r.MACROS if mm[0] in ('sk', 'tv', 'pv', 'pi', 'dynalloc1')]
PIECES = [('scanLoop', 28), ('nautyCall', 86)]
TOP = 'body'
