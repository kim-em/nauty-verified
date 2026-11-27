# Factoring of nauty.c's `firstterminal` for scripts/factor_clight.py.
MACROS = [
  ('sk', ['s'], '(.Ssequence .Sskip ?s)'),
  ('tv', ['x'], '(.Etempvar ?x tint)'),
  ('ix', ['p', 'a'], '(.Ederef (.Ebinop .Oadd (.Etempvar ?p (tptr tint)) ?a (tptr tint)) tint)'),
  ('gat', ['g', 'a'], '(.Ederef (.Ebinop .Oadd (.Evar ?g (tptr tint)) ?a (tptr tint)) tint)'),
  ('gats', ['g', 'a'], '(.Ederef (.Ebinop .Oadd (.Evar ?g (tptr tshort)) ?a (tptr tshort)) tshort)'),
  ('statsF', ['f', 't'], '(.Efield (.Ederef (.Evar id.«nauty:stats» (tptr (Tstruct id.«_1024» noattr))) (Tstruct id.«_1024» noattr)) ?f ?t)'),
  ('forLoopC', ['i', 'c', 'b'], '(.Ssequence (.Ssequence .Sskip (.Sset ?i (ci 0 tint))) (.Sloop (.Ssequence (.Ssequence .Sskip (.Sifthenelse ?c .Sskip .Sbreak)) ?b) (.Ssequence .Sskip (.Sset ?i (.Ebinop .Oadd (.Etempvar ?i tint) (ci 1 tint) tint)))))'),
]
PIECES = []
TOP = 'body'
