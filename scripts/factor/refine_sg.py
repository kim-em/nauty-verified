# Factoring of nausparse.c's `refine_sg` for scripts/factor_clight.py.
SK = '(.Ssequence .Sskip ?s)'
MACROS = [
  ('sk', ['s'], SK),
  ('tv', ['x'], '(.Etempvar ?x tint)'),
  ('pv', ['x'], '(.Etempvar ?x (tptr tulong))'),
  ('pi', ['x'], '(.Etempvar ?x (tptr tint))'),
  ('ix', ['p', 'a'], '(.Ederef (.Ebinop .Oadd (pi ?p) ?a (tptr tint)) tint)'),
  ('gix', ['p', 'a'], '(.Ederef (.Ebinop .Oadd (.Evar ?p (tptr tint)) ?a (tptr tint)) tint)'),
  ('setWord', ['s', 'a'],
   '(.Ederef (.Ebinop .Oadd (pv ?s) (.Ebinop .Oshr ?a (ci 6 tint) tint) (tptr tulong)) tulong)'),
  ('bitOf', ['b', 'a'],
   '(.Ederef (.Ebinop .Oadd (.Evar ?b (tarray tulong 64)) (.Ebinop .Oand ?a (ci 63 tint) tint) (tptr tulong)) tulong)'),
  ('isElement', ['s', 'b', 'a'],
   '(.Ebinop .One (.Ebinop .Oand (setWord ?s ?a) (bitOf ?b ?a) tulong) (ci 0 tint) tint)'),
  ('addElementB', ['s', 'b', 'a'],
   '(.Ssequence .Sskip (.Sassign (setWord ?s ?a) (.Ebinop .Oor (setWord ?s ?a) (bitOf ?b ?a) tulong)))'),
  ('delElementB', ['s', 'b', 'a'],
   '(.Ssequence .Sskip (.Sassign (setWord ?s ?a) (.Ebinop .Oand (setWord ?s ?a) (.Eunop .Onotint (bitOf ?b ?a) tulong) tulong)))'),
  ('mash', ['e'],
   '(.Sset id.«longcode» (.Ebinop .Oand (.Ebinop .Oadd (.Ebinop .Oxor (.Etempvar id.«longcode» tlong) (ci 27421 tint) tlong) ?e tlong) (ci 32767 tint) tlong))'),
  ('dynalloc1', ['gs', 'gp', 'elt', 'sz', 't1', 't2', 'msg', 'len'],
   '(.Ssequence .Sskip (.Sifthenelse (.Ebinop .Ogt (.Ecast ?sz tulong) (.Evar ?gs tulong) tint) (.Ssequence (.Ssequence .Sskip (.Sifthenelse (.Evar ?gs tulong) (.Ssequence .Sskip (.Scall none (.Evar id.«free» (tfun [(tptr Tvoid)] Tvoid)) [(.Evar ?gp (tptr ?elt))])) .Sskip)) (.Ssequence (.Ssequence .Sskip (.Sassign (.Evar ?gs tulong) ?sz)) (.Ssequence (.Ssequence (.Ssequence (.Ssequence .Sskip (.Scall (some ?t1) (.Evar id.«nauty_zalloc» (tfun [tulong] (tptr Tvoid))) [(.Ebinop .Omul (.Ecast ?sz tulong) (.Ecast (.Esizeof ?elt tulong) tulong) tulong)])) (.Sset ?t2 (.Ecast (.Ecast (.Etempvar ?t1 (tptr Tvoid)) (tptr ?elt)) (tptr ?elt)))) (.Sassign (.Evar ?gp (tptr ?elt)) (.Etempvar ?t2 (tptr ?elt)))) (.Sifthenelse (.Ebinop .Oeq (.Etempvar ?t2 (tptr ?elt)) (.Ecast (ci 0 tint) (tptr Tvoid)) tint) (.Ssequence .Sskip (.Scall none (.Evar id.«alloc_error» (tfun [(tptr tschar)] Tvoid)) [(.Evar ?msg (tarray tschar ?len))])) .Sskip)))) .Sskip))'),
  ('resetmarks', ['val', 'sz', 'arr', 't', 'ij'],
   '(.Ssequence (.Ssequence (.Ssequence .Sskip (.Sset ?t (.Evar ?val tshort))) (.Sassign (.Evar ?val tshort) (.Ebinop .Oadd (.Etempvar ?t tshort) (ci 1 tint) tint))) (.Sifthenelse (.Ebinop .Oge (.Etempvar ?t tshort) (ci 32000 tint) tint) (.Ssequence (.Ssequence (.Ssequence .Sskip (.Sset ?ij (.Ecast (ci 0 tint) tulong))) (.Sloop (.Ssequence (.Ssequence .Sskip (.Sifthenelse (.Ebinop .Olt (.Etempvar ?ij tulong) (.Evar ?sz tulong) tint) .Sskip .Sbreak)) (.Ssequence .Sskip (.Sassign (.Ederef (.Ebinop .Oadd (.Evar ?arr (tptr tshort)) (.Etempvar ?ij tulong) (tptr tshort)) tshort) (ci 0 tint)))) (.Ssequence .Sskip (.Sset ?ij (.Ebinop .Oadd (.Etempvar ?ij tulong) (ci 1 tint) tulong))))) (.Ssequence .Sskip (.Sassign (.Evar ?val tshort) (ci 1 tint)))) .Sskip))'),
  ('mk', ['arr', 'a'],
   '(.Ederef (.Ebinop .Oadd (.Evar ?arr (tptr tshort)) ?a (tptr tshort)) tshort)'),
]
PIECES = [
  ('queueLoop', 158), ('startLoop', 194), ('dist', 230), ('distLoop', 271), ('runD', 301),
  ('minD', 341), ('installD', 444), ('startsD', 475), ('fragLoopD', 569), ('runLoopD', 613),
  ('mainLoop', 690), ('selectLoop', 708), ('trivial', 776), ('edgeLoopT', 857),
  ('cellLoopT', 916), ('partLoopT', 944), ('revLoopT', 984), ('fixT', 1019),
  ('nontrivial', 1083), ('countLoop', 1118), ('edgeLoopN', 1131), ('clearLoop', 1165),
  ('cellLoopN', 1211), ('runN', 1235), ('minN', 1271), ('installN', 1374), ('startsN', 1404),
  ('fragLoopN', 1506), ('runLoopN', 1550), ('finish', 1621),
]
TOP = 'body'
