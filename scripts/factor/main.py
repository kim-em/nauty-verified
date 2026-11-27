# Factoring of dense_main.c's `main` for scripts/factor_clight.py.
MACROS = [
  ('sk', ['s'], '(.Ssequence .Sskip ?s)'),
  ('tv', ['x'], '(.Etempvar ?x tint)'),
  ('pi', ['x'], '(.Etempvar ?x (tptr tint))'),
  ('pl', ['x'], '(.Etempvar ?x (tptr tulong))'),
  ('ix', ['p', 'a'], '(.Ederef (.Ebinop .Oadd (pi ?p) ?a (tptr tint)) tint)'),
  ('rd', ['t'], '(.Scall (some ?t) (.Evar id.«nv_read» (tfun [] tlong)) [])'),
  ('wr', ['e'], '(.Scall none (.Evar id.«nv_write» (tfun [tlong] Tvoid)) [?e])'),
  ('za', ['t', 'e'], '(.Scall (some ?t) (.Evar id.«nauty_zalloc» (tfun [tulong] (tptr Tvoid))) [?e])'),
]
PIECES = [
  ('colourLoop', 69), ('edgeLoop', 123), ('cellLoop', 161), ('endLoop', 205),
  ('labOut', 257), ('orbOut', 279), ('cgOut', 301),
  ('tInput', 60), ('emptyG', 99), ('tPart', 152), ('tOpts', 228), ('tCall', 244), ('tOut', 248), ('tStats', 314),
]
TOP = 'body'
