LNSprover v.1.0 Readme file
===========================

LNSprover implements backwards proof search in modular linear nested
sequent calculi for normal and non-normal propositional modal
logics. It is based on the article

Lellmann, Pimentel: Proof search in nested sequent calculi. In: Davis,
Fenker, McIver, Voronkov (eds.): LPAR-20, pp.558-574, Springer (2015)

Input syntax
----------

Formulae as given by

  P | true | false | neg F | box F | F and F | F or F | F -> F

where P is a,b,c,... The usual conventions for omitting parentheses
are in place, i.e., the binding strength is: unary connectives > and >
or > ->.

Implemented logics
----------------

- The logics in the non-normal modal cube, i.e. extensions of
  classical modal logic E with any combination of the axioms 
  * C: regularity ( box a and box b -> box ( a and b) )
  * N: necessitation ( box true )
  * M: monotonicity ( box (a and b) -> box a and box b )

- The logics in the modal tesseract, i.e.g, extensions of monotone
  modal logic M with any combination of the axioms
  * P: ( neg box false )
  * D: ( box neg a -> neg box a )
  * T: ( box a -> a )
  * 4: ( box box a -> box a )
  * C: regularity ( box a and box b -> box ( a and b) )
  * N: necessitation ( box true )
  as well as the logics M5, MP5, M45, MP45, MD45, MC45, MCD45
  including the axiom 
  * 5 box neg a -> box neg box a
  Note that logic MCN is normal modal logic K, so e.g. MCNT4 is the
  logic KT4 = S4 in standard terminology. Also note that 5 implies N,
  so we have e.g. MC45 = MCN45 = K45 and MCD45 = MCND45 = KD45.

Usage
-----

Make sure you have SWI-Prolog installed (http://www.swi-prolog.org/)
and the files lnsprover.pl, derivation.tex and output.tex are in the
same folder. Start swipl and load the file LNSprover.pl. Run the
prover with

  ?- prv([Axioms],[Gamma],[Delta]).

where Gamma => Delta is the sequent you want to check and Axioms is a
list of axioms from

  cl, clc, cln, clm, mon, p, d, t, 4, 5, c, n

For extensions of classical modal logic E include cl, for the logics
in the tesseract include mon. The axioms prefixed with cl are those
for extensions of the non-normal cube, the remaining ones those for
the tesseract. IMPORTANT: for logics including axiom t switch on
Kleeneing of the propositional rules (see section Kleeneing below).

If the sequent is derivable, the prover displays the derivation and
writes it to a .tex file. If there is more than one derivation, hit ;
to search for the next one. Run latex on output.tex to obtain a pdf
showing all these derivations. For larger derivations you might need
to increase the paper size in the preamble of output.tex by replacing
the "a4paper" option in

  \usepackage[...,a4paper]{geometry}

with e.g. "a0paper".

Example
-------

- To check whether the sequent

  []A & []B => [](A & B)

  is derivable in classical modal logic with axioms N and C, type

  ?- prv([cl,cln,clc],[box a and box b],[box (a and b)]).

- To check whether

  [](A & B) => [][]B

  is derivable in monotone modal logic with axioms 4 and C, type

  ?- prv([mon,4,c],[box (a and b)],[box box b]).


Kleeneing
---------

By default the propositional rules are not Kleene'd (i.e., the
principal formulae are not copied into the premiss(es)). This can be
changed by typing

  ?- kleeneing.

Likewise, to turn Kleeneing off again type

  ?- nokleeneing.

IMPORTANT: For logics including the axiom T, switch on Kleeneing
to prevent loops in proof search.
