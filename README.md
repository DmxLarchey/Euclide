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

# Présentation du projet

Nous expliquons une preuve mécanisée en Coq/Rocq de 
l'irrationalité de √2, et plus généralement, de toute racine 
n-ième ⁿ√k qui n'est pas entière, c'est à dire, si k n'est pas
déjà de la forme rⁿ, un entier r élevé à la puissance n. Autrement dit,
nous démontrons que les seules racines n-ème rationnelles sont celles 
d'entiers élevés à la puissance n.

## Comment est décomposé ce projet

Il est composé de deux parties:
- une explication informelle à lire ci-dessous;
- cette explication est (hyper-)liée à une mécanisation Coq
  accessible dans le repertoire [`theories`](theories);
- le code Coq peut-être compilé puis exécuté dans une
  [interface utilisateur de Coq](https://coq.inria.fr/user-interfaces.html)
  telle que VsCoq ou encore CoqIDE.

## Compiler le projet

Pour compiler le projet, vous aurez besoin d'une version de
Coq suffisement récente, càd `Coq 8.13` ou ultérieure. Seule
une petite partie de la libraire standard livrée avec Coq est 
utilisée, donc il n'est pas nécéssaire d'installer des librairies 
supplémentaires.

Une installation de Coq via [opam](https://coq.inria.fr/opam-using.html),
ou encore via [Coq Platform](https://github.com/coq/platform)
est recommandée mais pas indispensable.
Un paquet standard Linux, Windows ou Mac devrait faire l'affaire.
Toutefois le script [`Makefile`](theories/Makefile) fournit a été
écrit pour Linux:

```console
git clone https://github.com/DmxLarchey/Euclide.git
cd Euclide/theories
make all
```

## Lire le code compilé

Les utilisateurs expérimentés de Coq peuvent lire le code
directement, càd, parcourir les fichiers:
1. [`divides.v`](theories/divides.v): notion de divisibilité et de primalité; 
2. [`gauss.v`](theories/gauss.v): théorème de Bezout, lemme de Gauss;
3. [`nth_root.v`](theories/nth_root.v): √2 et ⁿ√k.

dans cet ordre. Il y a aussi quelques fichiers d'outils:

- [`arith_ext.v`](theories/arith_ext.v): quelques additions utiles au module `Arith`;
- [`bounded_choice.v`](theories/bounded_choice.v): principe de choix fini;
- [`measure.v`](theories/measure.v): induction sur une mesure;
- [`gcd_rect.v`](theories/gcd_rct.v): principe de récurencce pour l'algorithme d'Euclide (PGCD).

Pour les utilisateurs moins à l'aise avec Coq, nous fournissons un plan
textuel de ces preuves mécanisées, avec des (hyper-)liens pour une
description moins formelle des étapes menant aux principaux résultats.

# Euclide et l'irrationalité de ⁿ√k pour k différent de rⁿ

Nous n'utilisons que les entiers de Peano du type `nat` pour les résultats
et preuves qui suivent. Les opérations arithmétiques sont définies dans
la librairie standard de Coq au sein des modules `Init` et `Arith`.
Attention, la valeur de `0^0` est définie comme étant `1` dans
cette librairie, même si mathématiquement, cette valeur est arbitraire 
car la fonction (x,y) ↦ xʸ n'est pas continue en (0,0). Ce
cas marginal n'est de toutes façons pas intéressant dans notre étude.

## Divisibilité et primalité

La notion de divisibilité, _d divise n_, avec la notation infixe d∣n, 
et l'ordre qu'elle induit sur les entiers, est l'outil fondamental dans 
les explications qui suivent. On utilisera aussi la notion de _divisibilité stricte_,
d divise n mais n ne divise pas d, notée d⇂n. Elles sont définies 
comme ceci [en Coq](theories/divides.v#L28):

```coq
Definition div d n := ∃q, q*d = n.
Notation "d ∣ n" := (div d n).

Definition sdiv d n := d∣n ∧ ¬ n∣d.
Notation "d ⇂ n" := (sdiv d n).
```

Les notions de nombres premiers en eux, et de nombres premiers,
en découlent:
- on rappelle que _p et q sont premiers entre eux_,
noté p ⊥ q ci-dessous, si seul 1 est un diviseur commun
à p et q (rappel: 1 divise tous les entiers);
- _p est premier_, noté `prime p` ci-dessous, si p>1 et
n'a que deux diviseurs, 1 et p lui-même.

## Irrationalité de √2

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
est rationnel seulement si k est de la forme rⁿ (r entier);
évidement dans ce cas on a ⁿ√k = r, et donc la réciproque est
triviale. Cela donne [en Coq](theories/nth_root.v#L301)

```coq
Theorem nth_root_rational__is_pow n k : nth_root_rational n k → ∃r, k = r^n.
```

La preuve de ce résultat est centrale dans cette présentation
et est détaillée dans la section suivante.

On peut maintenant utiliser le résultat précédent `nth_root_rational__is_pow`
pour démontrer l'irrationalité : on a réduit le problème à celui, 
d'établir qu'un entier k n'est pas de la forme rⁿ (avec r entier).
Pour cela, il suffit de procéder à un encadrement tel que k ∈ ]iⁿ,(1+i)ⁿ[ 
car il n'y a pas de d'entier de la forme rⁿ dans cet intervalle. En effet
la fonction i ↦ iⁿ est strictement croissante (quand n>0). 
[En Coq](theories/nth_root.v#L337) cela donne :

```coq
Theorem irrationality_criteria n k : (∃i, i^n < k < (1+i)^n) → nth_root_irrational n k.
```

Par des encadrements bien choisis, nous obtenons facilement des preuves que
³√7 ou encore ⁵√n (avec n ∈ ]32,243[) sont irrationnels. 
[En Coq](theories/nth_root.v#L350), on obtient :
 
```coq
Goal nth_root_irrational 3 7.
Goal ∀n, 32 < n < 243 → nth_root_irrational 5 n.
```

## ⁿ√k est rationnelle seulement si ⁿ√k est entier (càd k=rⁿ, r entier)

Pour obtenir ce résultat, on va démontrer le théorème de simplication suivant :
si dⁿ divise kⁿ alors d divise k oubien n=0. Ce résultat découle du lemme d'Euclide 
_si d est un entier premier_ car dans ce cas, en supposant n>0, comme d divise dⁿ, 
il est clair que d divise kⁿ et donc, comme il est premier, d divise k. 
L'argument est plus élaboré si d n'est pas un entier premier car on ne peut
pas directement appliquer le lemme d'Euclide dans ce cas.

Mais avant de passer à la preuve du théorème de simplification, voyons
rapidement comme on peut en déduire le théorème `nth_root_rational__is_pow`
càd ⁿ√k rationnel implique k=rⁿ. En effet, si ⁿ√k est rationnel alors 
on a k.qⁿ=pⁿ avec q≠0. Donc qⁿ|pⁿ et ainsi, par simplification, q|p oubien n=0: 
- si q|p alors il existe r tel que r.q=p et donc k=rⁿ;
- si n=0 alors k=1=1ⁿ.

Nous pouvons maintenant passer à la démonstration du théorème de simplification.
Bien sûr, on pourrait utiliser le [théorème fondamental de l'arithmétique](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_fondamental_de_l%27arithm%C3%A9tique),
càd la décomposition de tout nombre entier non nul en facteurs premiers, mais c'est 
un travail sensiblement plus long en Coq de démontrer l'existence et l'unicité
(à permutation près) d'une telle décomposition et ensuite de pouvoir comparer
de ces décompositions en cas de divisibilité. Ce n'est pas infaisable, mais
nous proposons un argument plus direct pour le résultat de simplification 
[en Coq](theories/nth_root.v#L251) :

```coq
Theorem div_pow_simplify n d k : d^n∣k^n → d∣k ∨ n=0.
```

_Démonstration:_ Nous allons procéder par induction
sur d, en utilisant l'_ordre de divisibilité stricte_ noté `_⇂_`. On
élimine d'emblée le cas n=0 qui est trivial et donc on se place
maintenant dans le cas n>0.

On démontre la propriété de d suivante : ∀k, dⁿ∣kⁿ → d∣k, en supposant, 
par induction, que la propriété est déjà établie pour tout e⇂d, 
càd on suppose IHd: ∀e, e⇂d → ∀k, eⁿ∣kⁿ → e∣k. A noter que la propriété
est supposée vraie pour tout k (càd quantifiée universellement sur k), 
ce qui est essentiel dans le raisonnement inductif ci-dessous.

Si d=0 ou d=1, le résultat est immédiat, sans utilisation de IHd. 
On se place donc dans le cas où d>1. Alors, on trouve un facteur premier 
de d, càd p tel que d = p.e où p est premier et e⇂d, en procédant par 
recherche exhaustive du plus petit diviseur de d dans l'interval ]1,d]. 
Remarque: si d est déjà premier alors p=d et e=1.

On a alors la chaine de divisibilité p∣d∣dⁿ∣kⁿ donc d'après Euclide 
on déduit p∣k, car  p est premier (contrairement à d qui ne l'est pas forcément). 
Ainsi, k=p.h et donc pⁿeⁿ=dⁿ∣kⁿ=pⁿhⁿ. En simplifiant
par pⁿ, on obtient eⁿ∣hⁿ et on applique l'hypothèse d'induction IHd
qui donne alors e∣h. En effet, e divise strictement d. 
On conclut que d=p.e divise k=p.h. _Fin de démonstration._

Cette démonstration utilise le [principe d'induction](theories/divides.v#L221) 
bien fondée suivant, plus précisément l'instance où `P d := ∀k, d^n∣k^n → d∣k` :

```coq
Theorem sdiv_induction (P : nat → Prop) : (∀d, (∀e, e⇂d → P e) → P d) → ∀d, P d.
```

qui est d'une forme similaire au principe d'induction forte sur l'ordre
naturel strict des entiers, à la différence près que l'ordre de divisibilité
strict `_⇂_` se substitue à l'ordre naturel strict `_<_` :

```coq
Theorem lt_induction (P : nat → Prop) : (∀d, (∀e, e<d → P e) → P d) → ∀d, P d.
```

La démonstration de `div_pow_simplify` utilise aussi l'existence d'un facteur premier 
dans tout nombre entier d>1. Comme expliqué ci-dessus, on le trouve en cherchant le plus 
petit diviseur de d dans l'intervalle ]1,d], qui existe forcément car d se divise lui-même,
bien qu'il ne soit pas forcément le plus petit à diviser d. Plus petit s'entend ici par
rapport l'ordre naturel sur les entiers. Ceci nécessite pour chaque 
entier i=2,...,d (dans cet ordre) de pouvoir choisir si i∣d ou au contraire 
si ¬i∣d, càd, on utilise la _décidabilité (faible)_ de la divisibilité, 
[en Coq](theories/divides.v#L159) :

```coq
Lemma div_wdec d n : d∣n ∨ ¬ d∣n.
``` 

Cette décidabilité (faible) peut se démontrer pex. en utilisant la division 
Euclidienne.

