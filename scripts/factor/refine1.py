# Factoring of naugraph.c's `refine1` (the `m == 1` refine) for scripts/factor_clight.py.
import importlib.util, os
_spec = importlib.util.spec_from_file_location('refine', os.path.join(os.path.dirname(__file__), 'refine.py'))
_r = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(_r)
MACROS = _r.MACROS + [
  ('bit1', ['b', 'a'], '(.Ederef (.Ebinop .Oadd (.Evar ?b (tarray tulong 64)) ?a (tptr tulong)) tulong)'),
  ('isElement1', ['s', 'b', 'a'], '(.Ebinop .One (.Ebinop .Oand (.Ederef (pv ?s) tulong) (bit1 ?b ?a) tulong) (ci 0 tint) tint)'),
  ('addElement1', ['s', 'b', 'a'],
   '(.Ssequence .Sskip (.Sassign (.Ederef (pv ?s) tulong) (.Ebinop .Oor (.Ederef (pv ?s) tulong) (bit1 ?b ?a) tulong)))'),
  ('delElement1', ['s', 'b', 'a'],
   '(.Ssequence .Sskip (.Sassign (.Ederef (pv ?s) tulong) (.Ebinop .Oand (.Ederef (pv ?s) tulong) (.Eunop .Onotint (bit1 ?b ?a) tulong) tulong)))'),
]
PIECES = [
  ('guard', 80), ('step', 119), ('trivial', 146), ('cellLoopT', 154), ('swapLoop', 192),
  ('trivSplit', 221), ('nontrivial', 277), ('cellLoopN', 307), ('cellN', 336),
  ('countRest', 371), ('splitN', 436), ('scanLoop', 459), ('placeLoop', 533), ('copyLoop', 555),
  ('fixN', 570), ('mainLoop', 78), ('finish', 583),
]
TOP = 'body'
