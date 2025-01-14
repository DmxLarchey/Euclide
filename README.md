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
nous démontrons que les seules racines n-ièmes rationnelles sont celles 
d'entiers élevés à la puissance n.

## Structure du projet

Il est composé de deux parties:
- une explication informelle à lire ci-dessous;
- cette explication est (hyper-)liée à une mécanisation Coq
  accessible dans le repertoire [`theories`](theories);
- le code Coq peut-être compilé puis exécuté dans une
  [interface utilisateur de Coq](https://coq.inria.fr/user-interfaces.html)
  telle que VsCoq ou encore CoqIDE.

## Compiler le projet

Pour compiler le projet, vous aurez besoin d'une version de
Coq pas trop ancienne, par exemple `Coq 8.13` ou une version ultérieure.
Au moment du dépôt de ce projet, la version courrante est `Coq 8.20`.
Seule une petite partie de la libraire standard livrée avec Coq est 
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

Le code est largement documenté. 
Les utilisateurs expérimentés de Coq peuvent le lire
directement, càd, parcourir les fichiers:
1. [`divides.v`](theories/divides.v): notion de divisibilité
1. [`prime.v`](theories/prime.v): notion de primalité;
1. [`bezout.v`](theories/gauss.v): théorème de Bezout puis lemme de Gauss;
1. [`gauss.v`](theories/gauss.v): lemme de Gauss en suivant [l'argumentaire d'Euclide VII](https://www.imo.universite-paris-saclay.fr/~daniel.perrin/CAPES/arithmetique/lemmeEuclide.pdf);
1. [`nth_root.v`](theories/nth_root.v): irrationalité de √2 et ⁿ√k.

plutôt dans cet ordre. Il y a aussi quelques fichiers d'outils ou de remarques annexes:
- [`arith_ext.v`](theories/arith_ext.v): quelques additions utiles au module `Arith`;
- [`bounded_choice.v`](theories/bounded_choice.v): principe de choix fini;
- [`measure.v`](theories/measure.v): induction sur une mesure;
- [`gcd_rect.v`](theories/gcd_rct.v): principe de récurrence pour l'algorithme d'Euclide (PGCD);
- [`primes_unbounded.v](theories/primes_unbounded.v): infinité des nombres premiers.

Pour les utilisateurs moins à l'aise avec Coq, nous fournissons un plan
textuel de ces preuves mécanisées, avec les (hyper-)liens pour les étapes
critiques. Nous obtenons ainsi une description un peu moins formelle des étapes 
menant aux principaux résultats.

# Euclide et l'irrationalité de ⁿ√k pour k différent de rⁿ

Dans le code Coq, **nous utilisons uniquement les entiers de Peano** du type `nat` pour 
les résultats et preuves qui suivent. Aussi ce type est implicite et n'est jamais rappelé dans 
les énoncés Coq. Toutefois, dans le discours informel ci-dessous, lorsque nous écrivons ⁿ√k, 
nous parlons d'un nombre qui peut ne pas être entier ni même rationnel. Pour simplifier
on pourrait le voir comme un nombre réel par exemple.

Nous rappelons que le type `nat` est le type inductif infini le plus simple, 
celui des entiers représentés en notation unaire (un seul chiffre):
```coq
Inductive nat : Type := O : nat | S : nat → nat.
```

Coq fournit une interface avec la représentation décimale et ainsi
il interprète le nombre `0` comme le terme `O` et le nombre `3` comme 
le terme `S (S (S O))`, càd `S` appliqué 3 trois fois à `O`. Coq
construit automatiquement le principe d'induction suivant
```coq
Theorem nat_ind (P : nat → Prop) : P O → (∀n, P n → P (S n)) → ∀n, P n.
```

généralement appelé _raisonnement par récurrence_. Nous verrons 
également d'autres principes d'induction sur le type `nat` plus
adaptés aux propriétés de la notion de divisibilité.

Les opérations arithmétiques sont définies dans
la librairie standard de Coq au sein des modules `Init` et `Arith`.
On peut noter que la valeur de `0^0` est définie comme étant `1` dans
cette librairie, même si mathématiquement, ce choix peut être vu comme 
arbitraire car la fonction (x,y) ↦ xʸ n'est pas continue en (0,0). Ce
cas marginal n'est pas significatif dans ce projet.

## Divisibilité et primalité

La notion de _divisibilité_ "d divise n", avec la notation infixe d∣n, 
et l'ordre qu'elle induit sur les entiers, est l'outil fondamental dans 
les explications qui suivent. On utilisera aussi la notion de _divisibilité stricte_
"d divise n mais n ne divise pas d", notée d⇂n. Elles sont définies 
comme ceci [en Coq](theories/divides.v#L28):

```coq
Definition div d n := ∃q, q*d = n.
Notation "d ∣ n" := (div d n).

Definition sdiv d n := d∣n ∧ ¬ n∣d.
Notation "d ⇂ n" := (sdiv d n).
```

Les notions de nombres premiers en eux et de nombres premiers,
en découlent:
- on rappelle que _x et y sont premiers entre eux_,
noté x ⊥ y ci-dessous, si seul 1 est un diviseur commun
à x et y (remarque: 1 divise tous les entiers);
- _p est premier_, noté `prime p` ci-dessous, si p≠1 et
n'a que deux diviseurs, 1 et p lui-même.

## Irrationalité de √2

Nous démontrons dans un premier temps l'irrationalité de √2 en utilisant 
le [lemme d'Euclide](https://fr.wikipedia.org/wiki/Lemme_d%27Euclide) 
qui affirme que si un nombre premier p divise x⋅y alors il divise x ou il divise y. Ce
qui s'exprime comme suit [en Coq](theories/nth_root.v#L35):

```coq
Lemma Euclid p x y : prime p → p∣x*y → p∣x ∨ p∣y.
```

Voir plus loin pour quelques détails sur la preuve
du lemme d'Euclide. Pour l'étude de √2 spécifiquement, 
on n'utilise que le cas particulier suivant (où p=2),
[en Coq](theories/nth_root.v#L145)

```coq
Lemma two_divides_square k : 2∣k*k → 2∣k.
```

_Démonstration de l'irrationalité de √2:_
soit une représentation rationnelle de √2, càd
a et b avec a ⊥ b et 2b² = a².
De 2b² = a², on déduit que 2 divise a²,
donc par Euclide, 2 divise a.
Ainsi a = 2r et donc 2b² = 4r² d'où b² = 2r². 
Ainsi 2 divise b² et par Euclide encore, 2 divise
b. Donc 2 divise à la fois a et b. Ils ne sont donc pas 
premiers entre eux, ce qui contredit l'hypothèse de départ
et conduit à une absurdité. _Fin de la démonstration._

[En Coq](theories/nth_root.v#L154) cela donne le théorème suivant:

```coq
Theorem root_2_not_rational a b : a ⊥ b → 2*b*b = a*a → False.
```

A noter que l'hypothèse a ⊥ b n'est pas strictement nécessaire
bien qu'elle soit essentielle au raisonnement ci-dessus. Pour
s'en défaire, il faut rajouter une induction, sous une forme
ou une autre, soit en montrant que toute fraction a/b à une 
représentation où a est premier avec b (calcul du PGCD pex), ou encore,
en raisonnant par induction bien fondée sur a avec pex l'ordre
de divisibilité stricte (voir ci-dessous).

## Identité de Bezout et lemme de Gauss

La preuve du lemme d'Euclide peut se déduire de sa généralisation,
le [lemme de Gauss](https://fr.wikipedia.org/wiki/Lemme_d%27Euclide): 
si d et x sont premiers entre eux, et d divise x⋅y 
alors d divise y. [En Coq](theories/gauss.v#L108):

```coq
Lemma Gauss d x y : d ⊥ x → d∣x*y → d∣y.
```

Le lemme de Gauss est lui-même conséquence de l'identité de Bezout
que l'on peut exprimer ainsi [en Coq](theories/gauss.v#L94):
```coq
Theorem Bezout : a ⊥ b ↔ ∃ u v u' v', u*a + v*b = 1 + u'*a + v'*b.
```

Cette forme un peu particulière est imposée par l'absence d'entiers
négatifs dans le type `nat`.
La preuve du [théorème de Bezout](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Bachet-B%C3%A9zout), 
pour sa partie non triviale (→), se fonde sur [l'algorithme d'Euclide](https://fr.wikipedia.org/wiki/Algorithme_d%27Euclide)
du calcul du PGCD, [étendu](https://fr.wikipedia.org/wiki/Algorithme_d%27Euclide_%C3%A9tendu) 
pour obtenir simultanément les coefficients de Bezout. Nous
n'entrons pas dans les détails de cette preuve ici. Cet algorithme
est toutefois fondamental en arithmétique: c'est l'un des tous premiers algorithmes 
découverts; c'est aussi le premier algorithme présenté et analysé par Donald Knuth 
dans son oeuvre de référence [_The Art of Computer Programming_](https://fr.wikipedia.org/wiki/The_Art_of_Computer_Programming).

## Rationalité ou irrationalité de ⁿ√k 

Nous définissons l'irrationalité d'une valeur x qui n'est pas représentable,
ni dans les entiers, ni même dans les rationnels, de la manière suivante: 
on utilise une propriété P(x) que devrait vérifier cette valeur et dont
on peut trouver une forme équivalent au sein du type `nat`.
Par exemple P(x) vaut x³ = 5 pour exprimer que x une
racine cubique de 5. Alors un rationnel x = a/b satisfait P(x) ssi (a/b)³ = 5 
ou encore ssi a³ = 5b³, qui est maintenant une équation représentable au sein
du type `nat` de Coq. 

Plus généralement, on utilise l'équation k⋅bⁿ = aⁿ pour exprimer que la
racine n-ième de k, càd ⁿ√k, est un nombre rationnel. A noter bien sûr que
a/b est une représentation rationnelle correcte seulement si b n'est pas nul.

On en déduit la définition suivante pour la rationalité de ⁿ√k, ainsi 
que pour son contraire l'irrationalité de ⁿ√k, [en Coq](theories/nth_root.v#L295):
```coq
Definition nth_root_rational n k := ∃ a b, b ≠ 0 ∧ k*b^n = a^n.
Definition nth_root_irrational n k := ¬ nth_root_rational n k.
```

Cette approche ne nécessite ni la définition de la fonction k ↦ ⁿ√k (impliquant au moins
celle des nombres algébriques), ni même la notion de nombre rationnel. On utilise seulement
la notion de représentation rationnelle via une fraction a/b composée de deux entiers(avec b≠0).

Nous démontrons le résultat suivant qui dit que ⁿ√k (k entier) 
admet une représentation rationnelle seulement si k est de 
la forme rⁿ (r entier). Cela donne [en Coq](theories/nth_root.v#L301)

```coq
Theorem nth_root_rational__is_pow n k : nth_root_rational n k → ∃r, k = r^n.
```

C'est le résultat principal de cette présentation
et sa preuve est détaillée dans la section suivante.
A noter que la réciproque est triviale:
si k=rⁿ alors r/1 est une représentation rationnelle de ⁿ√k.

On peut utiliser théorème `nth_root_rational__is_pow`
pour démontrer l'irrationalité. En effet, on a réduit le problème à celui 
d'établir qu'un entier k n'est pas de la forme rⁿ avec r entier.
Pour y parvenir, il suffit de procéder à un encadrement tel que k ∈ ]iⁿ,(1+i)ⁿ[ 
car il n'y a pas de d'entier de la forme rⁿ dans cet intervalle. En effet
la fonction i ↦ iⁿ est strictement croissante (quand n>0). 
[En Coq](theories/nth_root.v#L337) on obtient:
```coq
Theorem irrationality_criteria n k : (∃i, i^n < k < (1+i)^n) → nth_root_irrational n k.
```

Par des encadrements pertinents, nous obtenons maintenant facilement
des preuves que (par exemple) ³√7 ou encore ⁵√x (avec x ∈ ]32,243[) sont irrationnels. 
[En Coq](theories/nth_root.v#L350), on obtient:
 ```coq
Goal nth_root_irrational 3 7.
Goal ∀x, 32 < x < 243 → nth_root_irrational 5 x.
```

## ⁿ√k est rationnelle seulement si ⁿ√k est entier (càd k=rⁿ, r entier)

Pour obtenir ce résultat, on va démontrer le théorème de simplication suivant :
si dⁿ divise kⁿ alors d divise k ou bien n=0. Dans le _cas où d est un entier premier_,
ce résultat découle du lemme d'Euclide: en supposant n>0, comme d divise dⁿ, 
d divise donc aussi kⁿ et, comme il est premier, d divise donc k. 
L'argument est plus élaboré si d n'est pas un entier premier car on ne peut
alors pas appliquer directement le lemme d'Euclide.

Mais avant de passer à la preuve du théorème de simplification, voyons
rapidement comme on peut en déduire le théorème `nth_root_rational__is_pow`
càd ⁿ√k rationnel implique k=rⁿ pour un entier r. En effet, si ⁿ√k est rationnel alors 
on a k⋅bⁿ=aⁿ avec b≠0. Donc bⁿ|aⁿ et ainsi, par simplification, b|a ou bien n=0: 
- si b|a alors il existe un entier r tel que r⋅b=a, et donc k=rⁿ;
- si n=0 alors k=1=1ⁿ.

Nous pouvons maintenant passer à la démonstration du théorème de simplification.
Bien sûr, on pourrait utiliser le 
[théorème fondamental de l'arithmétique](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_fondamental_de_l%27arithm%C3%A9tique),
càd la décomposition de tout nombre entier non nul en facteurs premiers, mais c'est 
un travail sensiblement plus long en Coq de démontrer l'existence et l'unicité
(à permutation près) d'une telle décomposition et ensuite de pouvoir comparer
de ces décompositions en cas de divisibilité. Ce n'est pas infaisable, mais
nous proposons un argument plus direct pour le résultat de simplification 
[en Coq](theories/nth_root.v#L251):
```coq
Theorem div_pow_simplify n d k : d^n∣k^n → d∣k ∨ n=0.
```

_Démonstration:_ Nous allons procéder par induction
sur d, en utilisant l'_ordre de divisibilité stricte_ noté `_⇂_`. On
élimine d'emblée le cas n=0 qui est trivial et donc on se place
maintenant dans le cas n>0.

On démontre la propriété de d suivante : ∀k, dⁿ∣kⁿ → d∣k, en supposant, 
par induction, que la propriété est déjà établie pour tout e divisant strictement d, 
càd on suppose IHd: ∀e, e⇂d → ∀k, eⁿ∣kⁿ → e∣k. À noter: la propriété
est supposée vraie pour tout k (càd est quantifiée universellement/∀ sur k), 
ce qui est essentiel dans le raisonnement inductif ci-dessous.

Si d=0 ou d=1, le résultat est immédiat, sans utilisation de IHd. 
On se place donc dans le cas où d>1. Alors, on trouve un facteur premier 
de d, càd p tel que d = p⋅e où p est premier et e⇂d, en procédant par 
recherche exhaustive du plus petit diviseur de d dans l'interval ]1,d]. 
Remarque: si d est déjà premier alors p=d et e=1.

On a alors la chaine de divisibilité p∣d∣dⁿ∣kⁿ donc d'après Euclide 
on déduit p∣k, car  p est premier (contrairement à d qui ne l'est pas forcément). 
Ainsi, k=p⋅h et donc pⁿeⁿ=dⁿ∣kⁿ=pⁿhⁿ. En simplifiant
par pⁿ, on obtient eⁿ∣hⁿ et on applique l'hypothèse d'induction IHd
qui donne alors e∣h. C'est possible car e divise strictement d. 
On en conclut que d=p⋅e divise k=p⋅h. _Fin de la démonstration._

Cette démonstration utilise le [principe d'induction](theories/divides.v#L221) 
bien fondée suivant, plus précisément l'instance où `P d := ∀k, d^n∣k^n → d∣k`:
```coq
Theorem sdiv_induction (P : nat → Prop) : (∀d, (∀e, e⇂d → P e) → P d) → ∀d, P d.
```

qui est a une forme similaire au principe d'induction forte sur l'ordre
naturel strict des entiers, à la différence près que l'ordre de divisibilité
strict `_⇂_` remplace l'ordre naturel strict `_<_` :
```coq
Theorem lt_induction (P : nat → Prop) : (∀d, (∀e, e<d → P e) → P d) → ∀d, P d.
```

Nous insistons sur ces principes d'induction car ils sont constitutifs
et essentiels dans les systèmes de preuves constructifs fondés sur la 
théorie inductive des types, tels que celui de Coq.

La démonstration de `div_pow_simplify` utilise également l'existence d'un facteur 
premier dans tout nombre entier d>1. [En Coq](theories/nth_root.v#L225):
```coq
Corollary prime_factor' d : d = 0 ∨ d = 1 ∨ ∃ p e, prime p ∧ d = p*e ∧ e⇂d.
```

Comme suggéré ci-dessus, on le trouve par recherche exhaustive (finie) de plus 
petit diviseur de d dans l'intervalle ]1,d]. Il existe forcément car d divise d
lui-même, même s'il n'est pas nécessairement le plus petit possible. Plus petit 
s'entend ici par rapport l'ordre naturel sur les entiers. Ceci nécessite pour 
chaque entier i=2,...,d (dans cet ordre) de pouvoir discriminer entre le cas
où i divise d ou au contraire, i ne divise pas d. On utilise pour ça la _décidabilité (faible)_ 
de la divisibilité, [en Coq](theories/divides.v#L159):
```coq
Lemma div_wdec i d : i∣d ∨ ¬i∣d.
``` 

Cette décidabilité (faible) peut se démontrer par exemple en utilisant la 
division Euclidienne.

