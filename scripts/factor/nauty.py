# Factoring of nauty.c's `nauty` for scripts/factor_clight.py.
import importlib.util, os
_s = importlib.util.spec_from_file_location('refine', os.path.join(os.path.dirname(__file__), 'refine.py'))
_r = importlib.util.module_from_spec(_s); _s.loader.exec_module(_r)
MACROS = [mm for mm in _r.MACROS if mm[0] in ('sk', 'tv', 'pv', 'pi', 'dynalloc1')]
PIECES = [
  ('tSizes', 69), ('tZero', 103), ('zeroIf', 106), ('tMain', 213), ('tAlloc', 233),
  ('tTc', 503), ('tcIf', 506), ('tOpts', 543), ('tPtn', 683), ('ptnIf', 686), ('tInit', 841),
  ('tOrbits', 895), ('tStats', 913), ('tWork', 973), ('tRoot', 1015), ('tPost', 1021),
  ('postIf', 1024), ('tFree', 1079), ('freeIf', 1082),
]
TOP = 'body'
