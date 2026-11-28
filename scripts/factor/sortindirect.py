# Factoring of nausparse.c's `sortindirect` (sorttemplates.c, SORT_OF_SORT 3)
# for scripts/factor_clight.py.
SK = '(.Ssequence .Sskip ?s)'
MED = '''(sk (.Sifthenelse (.Ebinop .Ole ?a ?b tint)
  (sk (.Sifthenelse (.Ebinop .Ole ?b ?c tint)
    (.Ssequence (sk (.Sset ?t (.Ecast ?b tint))) (castT ?t))
    (sk (.Sifthenelse (.Ebinop .Ole ?c ?a tint)
      (.Ssequence (.Ssequence (sk (.Sset ?t (.Ecast ?a tint))) (castT ?t)) (castT ?t))
      (.Ssequence (.Ssequence (sk (.Sset ?t (.Ecast ?c tint))) (castT ?t)) (castT ?t))))))
  (sk (.Sifthenelse (.Ebinop .Ole ?a ?c tint)
    (.Ssequence (sk (.Sset ?t (.Ecast ?a tint))) (castT ?t))
    (sk (.Sifthenelse (.Ebinop .Ole ?c ?b tint)
      (.Ssequence (.Ssequence (sk (.Sset ?t (.Ecast ?b tint))) (castT ?t)) (castT ?t))
      (.Ssequence (.Ssequence (sk (.Sset ?t (.Ecast ?c tint))) (castT ?t)) (castT ?t))))))))'''
STK = ('(.Efield (.Ederef (.Ebinop .Oadd (.Evar id.«stack» (tarray (Tstruct id.«_1759» noattr) 40)) '
       '(.Etempvar id.«top» tint) (tptr (Tstruct id.«_1759» noattr))) (Tstruct id.«_1759» noattr)) ?f ?t)')
MACROS = [
  ('sk', ['s'], SK),
  ('tv', ['x'], '(.Etempvar ?x tint)'),
  ('pv', ['x'], '(.Etempvar ?x (tptr tint))'),
  ('ix', ['p', 'a'], '(.Ederef (.Ebinop .Oadd (pv ?p) ?a (tptr tint)) tint)'),
  ('dr', ['p'], '(.Ederef (pv ?p) tint)'),
  ('castT', ['t'], '(.Sset ?t (.Ecast (tv ?t) tint))'),
  ('med3', ['t', 'a', 'b', 'c'], MED),
  ('stk', ['f', 't'], STK),
  ('push', ['p', 'l'],
   '(.Ssequence (sk (.Sassign (stk id.«addr» (tptr tint)) ?p)) (.Ssequence (sk (.Sassign (stk id.«len» tint) ?l)) (sk (.Sset id.«top» (.Ebinop .Oadd (tv id.«top») (ci 1 tint) tint)))))'),
  ('swapThen', ['p', 'q', 'r'],
   '(.Ssequence (sk (.Sset id.«tmp1» (dr ?p))) (.Ssequence (sk (.Sassign (dr ?p) (dr ?q))) (.Ssequence (sk (.Sassign (dr ?q) (tv id.«tmp1»))) ?r)))'),
]
PIECES = [
  ('mainLoop', 21), ('insLoop', 49), ('shiftLoop', 69), ('pivot', 101),
  ('partLoop', 397), ('scanL', 403), ('scanR', 441), ('swapLoop', 529), ('swapLoop2', 583),
  ('pushes', 614),
]
TOP = 'body'
