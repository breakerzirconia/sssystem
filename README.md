**HEADS UP: this is a WIP, things might change!**

# Sssystem

Sssystem is a study of particular algebraic structures that extend additive abelian groups, called *Hemispheres*.

It is an acronym which expands, deliberately incorrectly, into **S**emi**s**phere-**system**, paying tribute to Enter Shikari.

### Preface

You may have heard that multiplication can be expressed in terms of addition and squaring.

$$a \cdot b = \frac{(a + b)^2 - a^2 - b^2}{2}$$

This is true, for example, in the usual number systems. However, I lied, it's not just addition and squaring that form this identity, but also halving and subtraction, which means negation, which (usually) signifies the presence of an additive identity (zero).

If we are to abstract away from concrete structures, we notice that we operate on an additive group (if we omit the word "usually" from the previous sentence). We would like to retrieve the usual properties of multiplication if we **define** it as the right hand-side of the identity above. We cannot yet, because it involves extra operations other than the ones defined in an additive group. We say that these additional operations form an *extra structure* on top of an already present additive group.

The purpose of this project is to study an additive group with said extra structure and recover all its necessary axioms / axiom schemata with which it becomes possible to derive the usual properties of multiplication. Enter: **Hemispheres**!

### What are hemispheres?

A *hemisphere* is a set $H$ endowed with
1. A binary operation $(+)$, pronounced **plus**, such that $(H, +)$ forms an additive *abelian* group. In other words,
   1. $(+)$ is **associative**: $`\forall x, y, z \in H \, . (x + y) + z = x + (y + z)`$.
   2. There exists a nullary constant $0$ such that $`\forall x \in H \, . x + 0 = 0 + x = x`$, pronounced **zero**.
   3. There exists a unary operation $(-)$ such that $`\forall x \in H \, . x + (-x) = (-x) + x = 0`$, pronounced **negation**.
   4. $(+)$ is **commutative**: $`\forall x, y \in H \, . x + y = y + x`$.
2. A unary operation $(\frown)$, pronounced **half**, for which the following set of properties holds.
   1. The fundamental $\frown$-property: $`\forall x \in H \, . \frown x + \frown x = x`$.
   2. Homomorphism: $`\forall x, y \in H \, . \frown (x + y) = \frown x + \frown y`$.
3. A unary operation $(\square)$, pronounced **square**, for which the following set of properties holds.
   1. $\square 0 = 0$.
   2. $`\forall x \in H \, . \square (\frown x) = \frown (\frown (\square x))`$.

Subtracion is defined canonically: $`x - y \; \coloneqq \; x + (- y)`$.

We then reference the Preface section and define multiplication as follows: $`x \cdot y \; \coloneqq \; \frown (\square (x + y) - \square x - \square y)`$.

#### Unital hemispheres

A *unital hemisphere* is a hemisphere $(H, 0, +, -, \square, \frown)$ with an additional nullary constant $1$ that is different from $0$, called **one** or **unity**, such that
1. $\square 1 = 1$.
2. $`\forall n \in \mathbb{N}, x \in H \, . \square (x + \frown^n 1) = \square x + \frown^n (x + x) + \frown^{2n} 1`$.

Where $`\mathbb{N} \coloneqq \{0, 1, 2, \dots\}`$ is the set of natural numbers, and $f^n (x)$ means "apply the function $f$ to the argument $x$ $n$ times".

A special constant $\frown 1$ is pronounced **one half**.

All the other constants formed by repeatedly applying $(\frown)$ to one half, i.e. $\frown \frown 1$, $\frown \frown \frown 1$, are pronounced **one quarter**, **one eighth**, and the list goes on.
