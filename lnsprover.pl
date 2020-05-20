/*
Copyright 2016 Bjoern Lellmann

    This file is part of LNSprover.

    LNSprover is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.
    LNSprover is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with LNSprover.  If not, see <http://www.gnu.org/licenses/>.
*/

/* operator definitions etc */
  :- op(400,fy,[neg,box]),
     op(500,xfy,and),
     op(600,xfy,or),
     op(700,xfy,->).

  :- use_module(library(lists)).

  :- set_prolog_flag(kleen,false).

/*   Linear nested sequents are lists of sequents;
     Sequents are pairs seq(Gamma,Delta) containing the antecedent Gamma 
     and the succedent Delta, both as lists of formulae.
     The predicate prv takes as first argument a list of axioms:
     - [] for propositional logic (always included)
     - mon, p, d, t, 4, 5, c, n for monotone modal logics
     - cl, clc, cln, clm for classical modal logics
     As second and third arguments it takes two lists Gamma,Delta of formulae,
     the left and right hand sides of the sequent.
*/

/* initialisation */
prv(Axioms,Gamma,Delta) :-
	open('derivation.tex',write,Stream1),
	write(Stream1,''),
	close(Stream1),!,
	prove(Axioms, [seq(Gamma,Delta)],T),
        pptree(T),
	open('derivation.tex',append,Stream),
	ppwrite(Stream,T),
	close(Stream).

/* Kleene'ing or not
 kleeneUnary is for unary connectives, kleeneBinary for binary ones
 Also implements loop checking by checking that the immediate subformulae are not there yet.
 By default, Kleene'ing is turned off. Assert the predicate kleeneing to turn it on.
*/
kleeneing :- set_prolog_flag(kleen,true).
nokleeneing :- set_prolog_flag(kleen,false).

kleeneUnary(Principal,List,Newlist,_,_) :-
	current_prolog_flag(kleen,false),
	select(Principal,List,Newlist).

kleeneUnary(_,List,Newlist,Subformula,Checklist) :-
	current_prolog_flag(kleen,true),!,
	\+ member(Subformula,Checklist),
	List = Newlist.

kleeneBinary(Principal,List,Newlist,_,_,_,_) :-
	current_prolog_flag(kleen,false),
	select(Principal,List,Newlist).
	
kleeneBinary(_,List,Newlist,Sub1,Checklist1,Sub2,Checklist2) :-
	current_prolog_flag(kleen,true),!,
	List = Newlist,
	\+ member(Sub1,Checklist1),
	\+ member(Sub2,Checklist2).

/*   The predicate prove takes as first argument a list of axioms as above, 
     as second a linear nested sequent and as third a proof tree.
     The proof trees are used to print the derivation; constructors are the
     names of the applied rules.
     As first argument they take 
     l (leaf), prop (propositional), mon (monotone), cl (classical) 
     to differentiate the different kinds of nesting.
*/

/* initial sequents */
prove(_,[seq(Gamma,Delta)|Hist],botL(l,[seq(Gamma,Delta)|Hist])) :- 
	member(false,Gamma),!.
prove(_,[seq(Gamma,Delta)|Hist],topR(l,[seq(Gamma,Delta)|Hist])) :-
	member(true,Delta),!.
prove(_,[seq(Gamma,Delta)|Hist],init(l,[seq(Gamma,Delta)|Hist])) :-
	member(F,Gamma), member(F,Delta),!.

/* propositional rules */
/* Completeness for the unKleene'd rules uses that contractions can be pushed
   to below modal rules 
*/
/* The difference between the Kleene'd and unKleene'd versions is handled
   by kleeneUnary and kleeneBinary respectively. 
*/

/* non-branching rules */
/* Negation */
prove(Axioms,[seq(Gamma,Delta)|Hist],negL(p,[seq(Gamma,Delta)|Hist],T)) :-
	member(neg A, Gamma),
	kleeneUnary(neg A, Gamma, Sigma, A, Delta),
        prove(Axioms,[seq(Sigma,[A|Delta])|Hist],T).
prove(Axioms,[seq(Gamma,Delta)|Hist],negR(p,[seq(Gamma,Delta)|Hist],T)) :-
	member(neg A, Delta),
	kleeneUnary(neg A, Delta, Pi, A, Gamma),
        prove(Axioms,[seq([A|Gamma],Pi)|Hist],T).

/* Conjunction */
prove(Axioms,[seq(Gamma,Delta)|Hist],conjL(p,[seq(Gamma,Delta)|Hist],T)) :-
	member(A and B, Gamma), 
	kleeneBinary(A and B, Gamma,Sigma,A,Gamma,B,Gamma),
        prove(Axioms,[seq([A,B|Sigma],Delta)|Hist],T).

/* Disjunction */
prove(Axioms,[seq(Gamma,Delta)|Hist],disjR(p,[seq(Gamma,Delta)|Hist],T)) :- 
	member(A or B, Delta), 
	kleeneBinary(A or B,Delta,Pi,A,Delta,B,Delta),
        prove(Axioms,[seq(Gamma,[A,B|Pi])|Hist],T).

/* Implication */
prove(Axioms,[seq(Gamma,Delta)|Hist],implR(p,[seq(Gamma,Delta)|Hist],T)) :- 
	member(A -> B, Delta),
	kleeneBinary(A -> B,Delta,Pi,A,Gamma,B,Delta),
        prove(Axioms,[seq([A|Gamma],[B|Pi])|Hist],T).

/* Branching rules */
/* Conjunction */
prove(Axioms,[seq(Gamma,Delta)|Hist],conjR(p,[seq(Gamma,Delta)|Hist],T1,T2)) :- 
	member(A and B, Delta), 
	kleeneBinary(A and B,Delta,Pi,A,Pi,B,Pi),
        prove(Axioms,[seq(Gamma,[A|Pi])|Hist],T1), 
        prove(Axioms,[seq(Gamma,[B|Pi])|Hist],T2).

/* Disjunction */
prove(Axioms,[seq(Gamma,Delta)|Hist],disjL(p,[seq(Gamma,Delta)|Hist],T1,T2)) :- 
	member(A or B, Gamma),
	kleeneBinary(A or B,Gamma,Sigma,A,Gamma,B,Gamma),
        prove(Axioms,[seq([A|Sigma],Delta)|Hist],T1),
        prove(Axioms,[seq([B|Sigma],Delta)|Hist],T2).

/* Implication */
prove(Axioms,[seq(Gamma,Delta)|Hist],implL(p,[seq(Gamma,Delta)|Hist],T1,T2)) :- 
	member(A -> B, Gamma),
	kleeneBinary(A -> B,Gamma,Sigma,A,Delta,B,Gamma),
        prove(Axioms,[seq([B|Sigma],Delta)|Hist],T1),
        prove(Axioms,[seq(Sigma,[A|Delta])|Hist],T2).

/* Modal rules */
/* T */
/* NOTE: needs kleeneing of the propositional rules for loop checking to work */
/* - otherwise e.g. proof search for box(p & q) => loops */
prove(Axioms,[seq(Gamma,Delta)|Hist],refl(p,[seq(Gamma,Delta)|Hist],T)) :-
	member(t,Axioms),
	member(box A, Gamma),
%        kleeneUnary(box A, Gamma, Sigma, A, Gamma),
	\+ member(A,Gamma),
	prove(Axioms,[seq([A|Gamma],Delta)|Hist],T).

/* box Right */
/* Principal formula is kept in implicit contraction */
prove(Axioms,[seq(Gamma,Delta)|Hist],boxRm(p,[seq(Gamma,Delta)|Hist],T)) :- 
	member(mon,Axioms),
        member( box B, Delta),
        proveUnfinished(Axioms,[],[seq([],[B]),seq(Gamma,Delta)|Hist],T).

/* P */
/* additional condition to prevent loops */
prove(Axioms,[seq(Gamma,Delta)|Hist],boxP(p,[seq(Gamma,Delta)|Hist],T)) :- 
	member(p,Axioms),
        \+ seq(Gamma,Delta) == seq([],[]),
        proveUnfinished(Axioms,[],[seq([],[]),seq(Gamma,Delta)|Hist],T).

/* d */
/* Principal formula is kept in implicit contraction */
prove(Axioms,[seq(Gamma,Delta)|Hist],boxD(p,[seq(Gamma,Delta)|Hist],T)) :- 
	member(d,Axioms),
        member(box A, Gamma),
        proveUnfinished(Axioms,[],[seq([A],[]),seq(Gamma,Delta)|Hist],T).

/* non-normal cube */
/* Box Right */
/* proveClassical_ takes (Axioms, List, dual(Seq1,Seq2), History, Tree) */
/* here List is a list of problematic rules which have been applied
   already (to prevent loops with c/n) */ 
/* dual(Seq1,Seq2) contains the two sequents in the binary nesting */
/* proveClassicalUnfinished implements unfinished rules */
/* proveClassicalFinished implements finished rules (to keep modal rules in a block) */
prove(Axioms,[seq(Gamma,Delta)|Hist],boxRcl(p,[seq(Gamma,Delta)|Hist],T)) :- 
	member(cl,Axioms),
        member(box B, Delta),
        select(box B, Delta, Pi),
        proveClassicalUnfinished(Axioms,[],dual(seq([],[B]),seq([B],[])),[seq(Gamma,Pi)|Hist],T).

/* monotonicity (clm) */
/* additional condition for loop check (checks that false is not already there) */
proveClassicalUnfinished(Axioms,L,dual(First,seq(Gamma2,Delta2)),Hist,boxClm(cl,dual(First,seq(Gamma2,Delta2)),Hist,T)) :- 
	member(clm,Axioms),
        \+ member(false,Gamma2),
        proveClassicalUnfinished(Axioms,L,dual(First,seq([false|Gamma2],Delta2)),Hist,T).

/* Box Left */
proveClassicalUnfinished(Axioms,L,dual(seq(Gamma1,Delta1),seq(Gamma2,Delta2)),[seq(Sigma,Pi)|Hist],boxLcl(cl,dual(seq(Gamma1,Delta1),seq(Gamma2,Delta2)),[seq(Sigma,Pi)|Hist],T1,T2)) :-
        member(cl,Axioms),
        member( box A, Sigma),
        select(box A, Sigma, Omega),
        proveClassicalFinished(Axioms,L,dual(seq([A|Gamma1],Delta1),seq(Gamma2,Delta2)),[seq(Omega,Pi)|Hist],T1),
        prove(Axioms,[seq(Gamma2,[A|Delta2]),seq(Omega,Pi)|Hist],T2).

/* necessitation */
proveClassicalUnfinished(Axioms,L,dual(First,Second),Hist,boxCln(cl,dual(First,Second),Hist,T)) :- 
	member(cln,Axioms),
	\+ member(clc,L),
        proveClassicalFinished(Axioms,[cln|L],dual(First,Second),Hist,T).

/* close (aka jump) */
/* Definitely closes the application of the sequent rule */
proveClassicalFinished(Axioms,_,dual(seq(Gamma1,Delta1),Second),Hist,close(clfin,dual(seq(Gamma1,Delta1),Second),Hist,T)) :-
        member(cl,Axioms),
        prove(Axioms,[seq(Gamma1,Delta1)|Hist],T).

/* regularity (C) */
proveClassicalFinished(Axioms,L,dual(First,Second),Hist,boxClc(clfin,dual(First,Second),Hist,T)) :- 
	member(clc,Axioms),
	\+ member(cln,L),
	list_to_set([clc|L],Newlist),
        proveClassicalUnfinished(Axioms,Newlist,dual(First,Second),Hist,T).

/* monotone ones */
/* provefinished and proveUnfinished include a marker to prevent
   loops with c / n in the form of a list storing which of these rules
   has already been applied.*/

/* necessitation */
/* is applied only if c was not applied before */
proveUnfinished(Axioms,N,Hist,boxMN(mon,Hist,T)) :- 
	member(n,Axioms),
	\+ member(c,N),
        provefinished(Axioms,[n|N],Hist,T).
                        
/* Box Left */
proveUnfinished(Axioms,N,[seq(Gamma,Delta),seq(Sigma,Pi)|Hist],boxLmon(mon,[seq(Gamma,Delta),seq(Sigma,Pi)|Hist],T)) :- 
	member(mon,Axioms),
        member(box A, Sigma),
        select(box A, Sigma, Omega),
        provefinished(Axioms,N,[seq([A|Gamma],Delta),seq(Omega,Pi)|Hist],T).

/* 4 */
/* Note: Loop checking is implemented by the jump rule below */
proveUnfinished(Axioms,N,[seq(Gamma,Delta),seq(Sigma,Pi)|Hist],boxM4(mon,[seq(Gamma,Delta),seq(Sigma,Pi)|Hist],T)) :- 
	member(4,Axioms),
        member( box A, Sigma),
        select(box A, Sigma,Omega),
        provefinished(Axioms,N,[seq([box A|Gamma],Delta),seq(Omega,Pi)|Hist],T).

/* 5 */
/* Note: loop checking implemented by the jump rule below */
proveUnfinished(Axioms,N,[seq(Gamma,Delta),seq(Sigma,Pi)|Hist],boxM5(mon,[seq(Gamma,Delta),seq(Sigma,Pi)|Hist],T)) :- 
	member(5,Axioms),
	member(box B, Pi),
	select(box B, Pi,Omega),
	provefinished(Axioms,N,[seq(Gamma,[box B|Delta]),seq(Sigma,Omega)|Hist],T).

/* rule c */
/* is applied only if n was not applied before */
provefinished(Axioms,N,Hist,monC(p,Hist,T)) :-
	member(c,Axioms),
	\+ member(n,N),
	list_to_set([c|N],L),
	proveUnfinished(Axioms,L,Hist,T).

/* jump rule */
/* loop checking is implemented by adding an "invisible sequent" invSeq(Gamma,Delta) */
/* containing the premiss Gamma => Delta of the current sequent rule into the history. */
/* The current sequent rule is closed only if its premiss is not an
   invisible sequent in the history. */ 
provefinished(Axioms,_,[seq(Gamma,Delta)|Hist],T) :-
	\+ member(seqInv(Gamma,Delta),Hist),
	prove(Axioms,[seq(Gamma,Delta),seqInv(Gamma,Delta)|Hist],T).

/* Pretty printing */
pptree(Term) :-
	pptreeAux(Term,0).

pptreeAux(Term,Nest) :-
	Term =.. [Op|[l,Hist]],
	Op == init,
	nl, tab(Nest+2), write(Op), write('('),
	ppseqlist(Hist),
	nl,tab(Nest+3),write(')').
pptreeAux(Term,Nest) :-
	Term =.. [Op|[l,Hist]],
	Op == botL,
	nl, tab(Nest+2), write(Op), write('('),
	ppseqlist(Hist),
	nl,tab(Nest+3),write(')').
pptreeAux(Term,Nest) :-
	Term =.. [Op|[l,Hist]],
	Op == topR,
	nl, tab(Nest+2), write(Op), write('('),
	ppseqlist(Hist),
	nl,tab(Nest+3),write(')').
pptreeAux(Term,Nest) :-
	Term =.. [Op|[p,Hist,X|List]],
	Op \== seq,
	nl, tab(Nest+2), write(Op), write('('),
	ppseqlist(Hist),
	pptreeList([X|List],Nest+2),
	nl, tab(Nest+3),write(')').
pptreeAux(Term,Nest) :-
	Term =.. [Op|[mon,Hist,X|List]],
	nl, tab(Nest+2), write(Op), write('('),
	ppmonseqlist(Hist),
	pptreeList([X|List],Nest+2),
	nl, tab(Nest+3), write(')').
pptreeAux(Term,Nest) :-
	Term =.. [Op|[cl,Dual,Hist,X|List]],
	nl, tab(Nest+2), write(Op), write('('),
	ppclassseqlist(Dual,Hist),
	pptreeList([X|List],Nest+2),
	nl, tab(Nest+3), write(')').
pptreeAux(Term,Nest) :-
	Term =.. [Op|[clfin,Dual,Hist,X|List]],
	nl, tab(Nest+2), write(Op), write('('),
	ppclassseqlist(Dual,Hist),
	pptreeList([X|List],Nest+2),
	nl, tab(Nest+3), write(')').

pptreeList([],_).
pptreeList([H|Tl],Nest) :-
	pptreeAux(H,Nest),
	pptreeList(Tl,Nest).

ppseqlist([]) :-
	write('').
ppseqlist([seqInv(_,_)|Hist]) :-
	ppseqlist(Hist).
ppseqlist([seq(Gamma,Delta)]) :-
	ppSeq(seq(Gamma,Delta)).
ppseqlist([seq(Gamma,Delta),Seq|Hist]) :-
	ppSeq(seq(Gamma,Delta)),
	write(' // '),
	ppseqlist([Seq|Hist]).

% ppclasseqlist([seq([],[b and a]),seq([b and a],[]),[seq([box(a and b)],[])]])

ppmonseqlist([]) :-
	write('').
ppmonseqlist([seqInv(_,_)|Hist]) :-
	ppmonseqlist(Hist).
ppmonseqlist([seq(Gamma,Delta),[]]) :-
	ppSeq(seq(Gamma,Delta)).
ppmonseqlist([seq(Gamma,Delta)|Hist]) :-
	ppSeq(seq(Gamma,Delta)),
	write(' /mon/ '),
	ppseqlist(Hist).

% ppclassseqlist: takes Dual,History
ppclassseqlist([]) :-
	write('').
ppclassseqlist(dual(First,Second),Hist) :-
	ppSeq(First),
	write(';'),
	ppSeq(Second),
	write(' /cl/ '),
	ppseqlist(Hist).

ppSeq(seq(Gamma,Delta)) :-
	write(Gamma),write('=>'),write(Delta).


/* writing LaTeX into the output file */
/* ppwrite/2 takes the stream and the proof tree */
ppwrite(Stream,Tree) :-
	nl(Stream),write(Stream,'\\['),nl(Stream),
	ppwriteAux(Stream,Tree,0),
	nl(Stream),write(Stream,'\\]'),nl(Stream),nl(Stream),!.

/* ppwriteAux/3 takes the stream, the proof tree, and the current nesting depth */
/* case distinction according to the last applied rule */
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[l,Seq]],
	Op == init, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\init]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[l,Seq]],
	Op == botL, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\botL]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[l,Seq]],
	Op == topR, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\topR]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
%ppwriteAux(Stream,Term,Nest) :-
%	Term =.. [Op|[p,Seq|List]],
%	Op == rem, tab(Stream,Nest+2),
%	write(Stream,'\\infer[\\W]{'),
%	ppwriteNest(Stream,Seq),write(Stream,'}{'), nl(Stream),
%	ppwriteList(Stream,List,Nest+2),
%	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
%ppwriteAux(Stream,Term,Nest) :-
%	Term =.. [Op|[p,Seq|List]],
%	Op == weakened, tab(Stream,Nest+2),
%	write(Stream,'\\infer[\\W]{'),
%	ppwriteNest(Stream,Seq),write(Stream,'}{'), nl(Stream),
%	ppwriteList(Stream,List,Nest+2),
%	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|List]],
	Op == refl, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\boxTm]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|List]],
	Op == boxRm, tab(Stream,Nest+2),
	write(Stream,'\\infer=[\\boxRm,\\ConR]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|List]],
	Op == boxP, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\boxP]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|List]],
	Op == boxD, tab(Stream,Nest+2),
	write(Stream,'\\infer=[\\boxD,\\ConL]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|List]],
	Op == boxRcl, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\boxRcl]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[cl,Dual,Hist|List]],
	Op == boxLcl, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\boxLcl]{'),
	ppwriteNest(Stream,cl,[Dual|Hist]),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[cl,Dual,Hist|List]],
	Op == boxClm, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\boxClm]{'),
	ppwriteNest(Stream,cl,[Dual|Hist]),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[cl,Dual,Hist|List]],
	Op == boxCln, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\boxCln]{'),
	ppwriteNest(Stream,cl,[Dual|Hist]),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[clfin,Dual,Hist|List]],
	Op == close, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\jump]{'),
	ppwriteNest(Stream,clfin,[Dual|Hist]),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[clfin,Dual,Hist|List]],
	Op == boxClc, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\boxClc]{'),
	ppwriteNest(Stream,clfin,[Dual|Hist]),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[mon,Seq|List]],
	Op == boxMN, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\boxMN]{'),
	ppwriteNest(Stream,mon,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[mon,Seq|List]],
	Op == boxLmon, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\boxLmon]{'),
	ppwriteNest(Stream,mon,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[mon,Seq|List]],
	Op == boxM4, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\boxMfour]{'),
	ppwriteNest(Stream,mon,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[mon,Seq|List]],
	Op == boxM5, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\boxMfive]{'),
	ppwriteNest(Stream,mon,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|List]],
	Op == monC, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\monC]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|List]],
	Op == negL, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\negL]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|List]],
	Op == negR, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\negR]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|List]],
	Op == conjL, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\conjL]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|List]],
	Op == conjR, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\conjR]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|List]],
	Op == disjL, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\disjL]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|List]],
	Op == disjR, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\disjR]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|List]],
	Op == implL, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\implL]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|List]],
	Op == implR, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\implR]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
/* catches all other cases */
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|List]],
	Op \== seq, tab(Stream,Nest+2),
	write(Stream,'\\infer['),write(Stream,Op), write(Stream,']{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').

/* LaTex nested sequents */
ppwriteNest(Stream,p,Seq) :-
        reverse(Seq,Seq2),
	ppwriteseqlist(Stream,Seq2).
ppwriteNest(Stream,mon,[Seq|Hist]) :-
        reverse(Hist,Hist2),
	ppwriteseqlist(Stream,Hist2),
	write(Stream,'\\lns[\\m]'),
	ppwriteseqlist(Stream,[Seq]).
ppwriteNest(Stream,cl,[dual(Seq1,Seq2)|Hist]) :-
        reverse(Hist,Hist2),
	ppwriteseqlist(Stream,Hist2),
	write(Stream,'\\lns[\\e] \\left['),
	ppwriteseqlist(Stream,[Seq1]),
	write(Stream,';'),
	ppwriteseqlist(Stream,[Seq2]),
	write(Stream,'\\right]').
ppwriteNest(Stream,clfin,[dual(Seq1,Seq2)|Hist]) :-
        reverse(Hist,Hist2),
	ppwriteseqlist(Stream,Hist2),
	write(Stream,'\\lns[\\e\\fin] \\left['),
	ppwriteseqlist(Stream,[Seq1]),
	write(Stream,';'),
	ppwriteseqlist(Stream,[Seq2]),
	write(Stream,'\\right]').

/* LaTeX a list of premisses */
ppwriteList(_,[],_).
ppwriteList(Stream,[H|[]],Nest) :-
	ppwriteAux(Stream,H,Nest).
ppwriteList(Stream,[H|Tl],Nest) :-
	ppwriteAux(Stream,H,Nest),
	nl(Stream),tab(Stream,Nest+2),write(Stream,'&'), nl(Stream),
	ppwriteList(Stream,Tl,Nest).

/* LaTeX a list of sequents */
ppwriteseqlist(Stream,[]) :- write(Stream,'').
ppwriteseqlist(Stream,[seqInv(_,_)|Hist]) :-
        ppwriteseqlist(Stream,Hist).
ppwriteseqlist(Stream,[seq(Gamma,Delta)|[]]) :-
	ppwriteFList(Stream,Gamma),write(Stream,' \\seq '),ppwriteFList(Stream,Delta).
ppwriteseqlist(Stream,[seq(Gamma,Delta),Seq|Hist]) :-
	ppwriteFList(Stream,Gamma),write(Stream,' \\seq '),ppwriteFList(Stream,Delta),
	write(Stream,' \\lns '),ppwriteseqlist(Stream,[Seq|Hist]).

/* LaTeX a list of formulae */
ppwriteFList(_,[]).
ppwriteFList(Stream,[Fml]) :-
	ppwriteFml(Stream,Fml).
ppwriteFList(Stream,[H,G|Tail]) :-
	ppwriteFml(Stream,H),write(Stream,','),ppwriteFList(Stream,[G|Tail]).

/* LaTeX a formula */
ppwriteFml(Stream,false) :-
	write(Stream,' \\bot ').
ppwriteFml(Stream,true) :-
	write(Stream,' \\top ').
ppwriteFml(Stream,Term) :-
	atom(Term), write(Stream,Term).
ppwriteFml(Stream,box(Fml)) :-
	write(Stream,'\\Box '),ppwriteFml(Stream,Fml).
ppwriteFml(Stream,neg(Fml)) :-
	write(Stream,' \\neg '),ppwriteFml(Stream,Fml).
ppwriteFml(Stream,and(Fml1,Fml2)) :-
	write(Stream,'('),ppwriteFml(Stream,Fml1),
	write(Stream,' \\land '),
	ppwriteFml(Stream,Fml2),write(Stream,')').
ppwriteFml(Stream,or(Fml1,Fml2)) :-
	write(Stream,'('),ppwriteFml(Stream,Fml1),
	write(Stream,' \\lor '),
	ppwriteFml(Stream,Fml2),write(Stream,')').
ppwriteFml(Stream,->(Fml1,Fml2)) :-
	write(Stream,'('),ppwriteFml(Stream,Fml1),
	write(Stream,' \\to '),
	ppwriteFml(Stream,Fml2),write(Stream,')').
