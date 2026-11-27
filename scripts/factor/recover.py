# Factoring of nauty.c's `recover` for scripts/factor_clight.py.
import importlib.util, os
_s = importlib.util.spec_from_file_location('ft', os.path.join(os.path.dirname(__file__), 'firstterminal.py'))
_r = importlib.util.module_from_spec(_s); _s.loader.exec_module(_r)
MACROS = _r.MACROS
PIECES = []
TOP = 'body'
