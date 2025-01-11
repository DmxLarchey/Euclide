```coq
(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)
```

# Euclide et l'irrationalité de ⁿ√k pour k différent de rⁿ

Nous n'utilisons que les entiers de Peano du type `nat` pour les résultats
et preuves qui suivent. Les opérations arithmétiques sont définies dans
la librairie standard de Coq au sein des modules `Init` et `Arith`.
Attention, la valeur de `0^0` est définie comme étant `1` dans
cette librairie, même si mathématiquement, cette valeur est arbitraire 
car la fonction (x,y) ↦ xʸ n'est pas continue en (0,0). Ce
cas marginal n'est de toutes façons pas intéressant dans notre étude.

## Irrationalité de √2

La notion de divisibilité _d divise n_, notée d∣n, et l'ordre qu'elle
induit sur les entiers, est l'outil fondamental dans les explications 
qui suivent et est définie comme ceci [en Coq](theories/divides.v#L28):

```coq
Definition div d n := ∃q, q*d = n.
Infix "∣" := div.
```

Les notions de nombres premiers en eux, et de nombres premiers,
en découlent:
- on rappelle que _p et q sont premiers entre eux_, noté
noté p ⊥ q ci-dessous, si seul 1 est un diviseur commun
à p et q (rappel: 1 divise tous les entiers);
- _p est premier_, noté `prime p` ci-dessous, si p≠1 et
n'a que deux diviseurs, 1 et p lui-même.

Nous démontrons dans un premier temps l'irrationalité de √2 en utilisant 
le [lemme d'Euclide](https://fr.wikipedia.org/wiki/Lemme_d%27Euclide) 
qui dit que si un nombre premier p divise x.y alors il divise x ou il divise y. Ce
qui donne [en Coq](theories/nth_root.v#L35):

```coq
Lemma Euclid p x y : prime p → p∣x*y → p∣x ∨ p∣y.
```

Voir plus loin pour quelques détails sur la preuve
du lemme d'Euclide. Pour l'étude de √2 spécifiquement, 
on n'utilise que le cas particulier suivant (où p=2),
[en Coq](theories/nth_root.v#L145)

```coq
Lemma two_divides_square n : 2∣n*n → 2∣n.
```

_Démonstration de l'irrationalité de √2:_
soit une représentation rationnelle de √2, càd
p et q avec p ⊥ q et 2q² = p².
De 2q² = p², on déduit que 2 divise p²,
donc par Euclide, 2 divise p.
Ainsi p = 2r et donc 2q² = 4r² d'où q² = 2r². 
Ainsi 2 divise q² et par Euclide encore, 2 divise
q. Donc 2 divise à la fois p et q. Ils ne sont donc pas 
premiers entre eux, ce qui contredit l'hypothèse de départ
et conduit à une absurdité. _Fin de démonstration._

[En Coq](theories/nth_root.v#L154) cela donne le théorème suivant:

```coq
Theorem root_2_not_rational p q : p ⊥ q → 2*q*q = p*p → False.
```

A noter que l'hypothèse p ⊥ q n'est pas strictement nécessaire
bien qu'elle soit essentielle au raisonnement ci-dessus. Pour
s'en défaire, il faut rajouter une induction, sous une forme
ou une autre, soit en montrant que toute fraction p/q à une 
représentation où p ⊥ q (calcul du PGCD pex), ou encore,
en raisonnant par induction bien fondée sur p avec pex l'ordre
de divisibilité stricte (voir ci-dessous).

## Identité de Bezout et lemme de Gauss

La preuve du lemme d'Euclide peut se déduire de sa généralisation,
le [lemme de Gauss](https://fr.wikipedia.org/wiki/Lemme_d%27Euclide): 
si d et x sont premiers entre eux, et d divise x.y 
alors d divise y. [En Coq](theories/gauss.v#L108):

```coq
Lemma Gauss d x y : d ⊥ x → d∣x*y → d∣y.
```

Le lemme de Gauss est lui-même conséquence de l'identité de Bezout
que l'on peut exprimer ainsi [en Coq](theories/gauss.v#L94)), 
en n'utilisant que des entiers de `nat`:

```coq
Theorem Bezout : a ⊥ b ↔ ∃ u v u' v', u*a + v*b = 1 + u'*a + v'*b.
```

La preuve du [théorème de Bezout](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Bachet-B%C3%A9zout), 
pour sa partie non triviale (→), se fonde sur [l'algorithme d'Euclide](https://fr.wikipedia.org/wiki/Algorithme_d%27Euclide_%C3%A9tendu) 
du calcul du PGCD, généralisé pour calculer un même temps les coefficients de Bezout. Nous
n'entrons pas dans les détails de cette preuve ici. Cet algorithme
est fondamental: c'est l'un des tous premiers algorithmes découverts; 
c'est aussi le premier exemple utilisé par D. Knuth dans [_The Art of
Computer Programming_](https://fr.wikipedia.org/wiki/The_Art_of_Computer_Programming).

## Rationalité ou irrationalité de ⁿ√k 

Nous définissons l'irrationalité d'une valeur x qui n'est pas représentable,
ni dans les entiers, ni même dans les rationnels, de la manière suivante: 
on utilise une propriété P(x) que devrait vérifier cette valeur et dont
on peut trouver une forme équivalent au sein du type `nat`.
Par exemple P(x) vaut x³ = 5 pour exprimer que x une
racine cubique de 5. Alors un rationnel x = p/q satisfait P(x) ssi (p/q)³ = 5 
ou encore ssi p³ = 5q³, qui est maintenant une équation représentable au sein
du type `nat` de Coq. 

Plus généralement, on utilise l'équation k.qⁿ = pⁿ pour exprimer que la
racine n-ième de k, càd ⁿ√k, est un nombre rationnel. A noter bien sûr que
p/q n'est un rationnel que si q n'est pas nul.

On en déduit la définition suivante pour la rationalité de ⁿ√k, ainsi 
que pour son contraire l'irrationalité de ⁿ√k, [en Coq](theories/nth_root.v#L295):

```coq
Definition nth_root_rational n k := ∃ p q, q ≠ 0 ∧ k*q^n = p^n.
Definition nth_root_irrational n k := ¬ nth_root_rational n k.
```

Nous démontrons le résultat suivant qui dit que ⁿ√k (k entier) 
est rationnel seulement si k est de la forme rⁿ (r entier).
Évidement dans ce cas on a ⁿ√k = r et donc la réciproque est
triviale, [en Coq](theories/nth_root.v#L301)

```coq
Theorem nth_root_rational__is_pow n k : nth_root_rational n k → ∃r, k = r^n.
```

La preuve de ce résultat est centrale et est détaillée dans la section suivante.

Pour démontrer que k entier n'est pas de la forme rⁿ (k et r entiers), il est
plus pratique de procéder à un encadrement de k de la forme k ∈ ]iⁿ,(1+i)ⁿ[ 
car il n'y a pas de d'entier de la forme rⁿ dans cet intervalle. En effet
la fonction i ↦ iⁿ est strictement croissante. [En Coq](theories/nth_root.v#L337) 
cela donne :

```coq
Theorem irrationality_criteria n k : (∃i, i^n < k < (1+i)^n) → nth_root_irrational n k.
```

Par de bons encadrements, nous obtenons facilement des preuves que
³√7 ou encore ⁵√n (avec n ∈ ]32,243[) sont irrationnels. [En Coq](theories/nth_root.v#L350),
ça donne :
 
```coq
Goal nth_root_irrational 2 2.
Goal nth_root_irrational 3 7.
Goal nth_root_irrational 5 132.
Goal nth_root_irrational 2 255.
Goal ∀n, 27 < n < 64 → nth_root_irrational 3 n.
Goal ∀n, 32 < n < 243 → nth_root_irrational 5 n.
```

## ⁿ√k est rationnelle seulement si k est de la forme rⁿ

Pour obtenir ce résultat, on va démontrer le résultat de simplication suivant
[en Coq](theories/nth_root.v#L251) :

```coq
Theorem div_pow_simplify n d k : d^n∣k^n → d∣k ∨ n=0.
```

Le résultat découle du lemme d'Euclide si d est premier car dans ce
cas, en supposant n > 0, comme d∣d^n, il est clair que d∣k^n et
donc, comme il est premier, d∣k. C'est beaucoup moins trivial si
d n'est pas premier car on ne peut pas appliquer le lemme d'Euclide
dans ce cas.

Bien sûr, on peut utiliser le [théorème fondamental de l'arithmétique](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_fondamental_de_l%27arithm%C3%A9tique),
la division de tout nombre entier non nul en facteurs premiers, mais c'est beaucoup
de travail en Coq. 

_Démonstration:_ Nous proposons au contraire de procéder par induction
sur d, en utilisant l'ordre de divisibilité stricte noté `_ ⇂ _`. On
élimine d'emblée le cas n=0 qui est trivial et donc on suppose n>0.

On démontre donc ∀k, dⁿ∣kⁿ → d∣k en supposant, par induction, que la propriété
est déjà établie pour tout e⇂d, càd IH: ∀e, e⇂d → ∀k, eⁿ∣kⁿ → e∣k.

Si d=0 ou d=1, le résultat est immédiat, sans utilisation de IH. 
On se place donc dans le cas où d>1. Alors, on trouve un facteur premier 
de d, càd p tel que d = p.e où p est premier et e⇂d, en procédant par 
recherche exhaustive du premier diviseur de d dans l'interval ]1,d]. 
Remarque: si d est déjà premier alors p=d et e=1.

On a alors p∣d∣dⁿ∣kⁿ donc d'après Euclide on déduit p∣k. Ainsi, k = p.h
et donc pⁿeⁿ=dⁿ∣kⁿ=pⁿhⁿ. En simplifiant, on obtient eⁿ∣hⁿ et on applique
l'hypothèse d'induction IH qui donne alors e∣h. On en conclut que d=p.e∣p.h=k.
_Fin de démonstration._

Cette preuve fonctionne en utilisant le [principe d'induction](theories/divides.v#L221) 
bien fondée suivant:

```coq
Theorem sdiv_induction (P : nat → Prop) : (∀n, (∀d, d⇂n → P d) → P n) → ∀n, P n.
```

qui est d'une forme similaire au principe d'induction forte sur l'ordre
naturel strict des entiers, à la différence près où `_ ⇂ _` se substitue à `_ < _` :

```coq
Theorem lt_induction (P : nat → Prop) : (∀n, (∀d, d<n → P d) → P n) → ∀n, P n.
```

La preuve utilise aussi l'existence d'un facteur premier dans tout nombre
entier d > 1. Comme expliqué ci-dessus, on le trouve en cherchant le premier 
diviseur de d dans l'interval ]1,d], qui existe forcément car d∣d lui-même, mais
n'est pas forcément le premier. Par premier, on étend ici le plus petit pour
l'ordre naturel sur les entiers. Ceci nécessite pour chaque entier i∈]1,d]
de pouvoir choisir si i∣d ou au contraire si ¬i∣d, càd, la décidabilité
de la divisibilité, que l'on démontre pex. en utilisant la division
Euclidienne [en Coq](theories/divides.v#L159):

```coq
Lemma div_wdec d n : d∣n ∨ ¬ d∣n.
``` 
