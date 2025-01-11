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

Nous démontrons dans un premier temps l'irrationalité de √2
en utilisant le lemme d'Euclide qui dit que si un nombre
premier p divise x.y alors il divise x ou il divise y. Ce
qui donne en Coq:

```coq
Lemma Euclid p x y : prime p → p∣x*y → p∣x ∨ p∣y.
```

Voir plus loin pour quelques détails sur la preuve
du lemme d'Euclide. Pour l'étude de √2 spécifiquement, 
on n'utilise que le cas particulier suivant (2 est premier):

```coq
Lemma two_divides_square n : 2∣n*n → 2∣n.
```

Soit une représentation rationnelle de √2, càd
p et q avec p et q premiers entre eux et 2q² = p².

De 2q² = p², on déduit que 2 divise p²,
donc par Euclide, 2 divise p.
Ainsi p = 2r et donc 2q² = 4r² d'où q² = 2r². 
Ainsi 2 divise q² et par Euclide encore, 2 divise
q. Donc 2 divise à la fois p et q. Ils ne peuvent
donc pas être premiers entre eux, ce qui est
absurde. En Coq celà donne le théorème suivant:

```coq
Theorem root_2_not_rational p q : p ⊥ q → 2*q*q = p*p → False.
```

## Identité de Bezout et lemme de Gauss

La preuve du lemme d'Euclide peut se déduire de sa généralisation,
le lemme de Gauss: si d et x sont premiers entre eux et d divise x.y
alors d divise y. En Coq:

```coq
Lemma Gauss d x y : d ⊥ x → d∣x*y → d∣y.
```

Le lemme de Gauss est lui-même conséquence de l'identité de Bezout
que l'on peut exprimer ainsi en Coq, en n'utilisant que des
entiers de `nat`:

```coq
Theorem Bezout : a ⊥ b ↔ ∃ u v u' v', u*a + v*b = 1 + u'*a + v'*b.
```

## Rationalité ou irrationalité de ⁿ√k 

Nous définissons l'irrationalité d'une valeur x qui n'est pas représentable,
ni dans les entiers, ni même dans les rationels, de la manière suivante: 
on utilise une propriété P(x) que devrait vérifier cette valeur et dont
on peut trouver une forme équivalent au sein du type `nat`.
Par exemple P(x) vaut x² = 2 pour exprimer que x une
racine carrée de 2. Alors un rationel x = p/q satisfait P(x) ssi (p/q)² = 2 
ou encore ssi p² = 2q², qui est maintenant une équation représentable au sein
du type `nat` de Coq. 

Plus généralement, on utilise l'équation qⁿ.k = pⁿ pour exprimer que la
racine n-ième de k, càd ⁿ√k, est un nombre rationel. A noter bien-sûr que
p/q n'est un rationel que si q n'est pas nul. 

On en déduit les deux définitions suivant pour la rationalité, et son
contraire l'irrationalité, de ⁿ√k.

```coq
Definition nth_root_rational n k := ∃ p q, q ≠ 0 ∧ q^n*k = p^n.
Definition nth_root_irrational n k := ¬ nth_root_rational n k.
```

Nous démontrons le résultat suivant qui dit que ⁿ√k (k entier) 
est rationel seulement si k est de la forme rⁿ (r entier).
Evidement dans ce cas on a ⁿ√k = r et donc la réciproque est
triviale.

```coq
Theorem nth_root_rational__is_pow n k : nth_root_rational n k → ∃r, k = r^n.
```

Pour prouver que k entier n'est pas de la forme rⁿ (k et r entiers), il est
plus pratique de procéder à un encadrement de k de la forme k ∈ ]iⁿ,(1+i)ⁿ[ 
car il n'y a pas de d'entier de la forme rⁿ dans cet interval. En effet
la fonction i ↦ iⁿ est strictement croissante. En Coq celà donne:

```coq
Theorem irrationality_criteria n k : (∃i, i^n < k < (1+i)^n) → nth_root_irrational n k.
```

Par de bon encadrement nous obtenons donc facilement des preuves que
³√7 ou encore ⁵√n (avec n ∈ ]32,243[) sont irrationels. En Coq, celà
donne:
 
```coq
Goal nth_root_irrational 2 2.
Goal nth_root_irrational 3 7.
Goal nth_root_irrational 5 132.
Goal nth_root_irrational 2 255.
Goal ∀n, 27 < n < 64 → nth_root_irrational 3 n.
Goal ∀n, 32 < n < 243 → nth_root_irrational 5 n.
```

