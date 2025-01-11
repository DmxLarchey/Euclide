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

## Rationalité ou irrationalité de ⁿ√k 

Nous n'utilisons que les entiers de Peano du type `nat` pour les résultats
et preuves qui suivent. Les opérations arithmétiques sont définies dans
la librairie standard de Coq au sein des modules `Init` et `Arith`.
Attention, la valeur de `0^0` est définie comme étant `1` dans
cette librairie, même si mathématiquement, cette valeur est arbitraire 
car la fonction (x,y) ↦ xʸ n'est pas continue en (0,0). Ce
cas marginal n'est de toute façons pas intéressant dans notre étude.

Nous définissons l'irrationalité d'une valeur x qui n'est pas représentable,
ni dans les entiers, ni même dans les rationels, de la manière suivante: 
Soit P(x) une propriété que devrait vérifier cette valeur, pas nécessairement
caractéristique de x. Par exemple P(x) vaut x² = 2 pour exprimer que x une
racine carrée de 2. Alors un rationel x = p/q satisfait P(x) ssi (p/q)² = 2 
ou encore ssi p² = 2q², qui est maintenant une équation représentable dans le 
/type `nat` de Coq. 

Plus généralement, on utilise l'équation qⁿ.k = pⁿ pour exprimer que la
racine n-ième de k, càd ⁿ√k, est un nombre rationel. A noter bien-sûr que
p/q n'est un rationel que si q n'est pas nul. 

On en déduit les deux définitions suivant pour la rationalité, et son
contraire l'irrationalité, de ⁿ√k.

```coq
Definition nth_root_rational n k := ∃ p q, q ≠ 0 ∧ q^n*k = p^n.
Definition nth_root_irrational n k := ¬ nth_root_rational n k.
```

## Irrationalité de √2

Nous démontrons dans un premier temps l'irrationalité de √2
en utilisant le lemme d'Euclide qui dit que si un nombre
premier p divise x.y alors il divise x ou il divise y. Ce
qui donne en Coq:

```coq
Lemma Euclid p x y : prime p → p∣x*y → p∣x ∨ p∣y.
```

En particulier, on en déduit le cas particulier suivant,
car 2 est premier:

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
absurde.

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

## Généralisation à ⁿ√k

```coq
Theorem nth_root_rational__is_pow n k : nth_root_rational n k → ∃r, k = r^n.
```

```coq
Theorem irrationality_criteria n k : (∃i, i^n < k < (1+i)^n) → nth_root_irrational n k.
```

