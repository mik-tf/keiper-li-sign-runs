---
title: "Sign runs and the density of sign changes of Keiper-Li second differences"
author: "Michaël Perreault"
date: "2026-11-23"
format: "article"
toc: false
header_footer_policy: "all"
footer: "© 2026 Michaël Perreault · CC BY 4.0"
pageof: true
date_footer: "YYYY-MM-DD"
header_title: "Sign runs and the density of sign changes of Keiper-Li second differences"
header-includes:
  - \usetikzlibrary{arrows.meta}
  - \renewcommand{\thetheorem}{\Alph{theorem}}
---

**Abstract.** Let $c_n=\lambda_{n+1}-2\lambda_n+\lambda_{n-1}$ be the second differences of the Li coefficients $\lambda_n$. It is known unconditionally that $c_n$ changes sign infinitely often, with $c_1,\dots,c_{117}>0>c_{118}$. We study how long a run of one sign can be and how often the sign changes; all results on these questions are conditional. Assuming the Riemann hypothesis (RH), we prove that every window of $1573$ consecutive indices contains both a positive and a negative $c_n$, so every run of one sign has length at most $1572$; and that each sign has runs of length at least $312$, with positive lower density. Assuming RH and a linear independence hypothesis on the angles $\theta_k=2\arctan(1/(2\gamma_k))$ of the first $700$ zeros $\tfrac12+i\gamma_k$, runs of $392$ consecutive positive values, and of $392$ negative values, occur with positive lower density; with the first $1400$ zeros, runs of $476$. Assuming RH and the independence of $\pi$ and all $\theta_k$ over $\mathbb{Q}$, counted with multiplicity, the sign changes of $c_n$ have a density $\delta$, and $\delta/(\theta_1/\pi)$ lies in $[0.969481285147,\,0.971027176735]$, in particular below $1$. The constants in the theorems are verified in ball arithmetic, and the code is public.

```{=latex}
\begingroup\small
This work is licensed under the Creative Commons Attribution 4.0 International License (CC BY 4.0), https://creativecommons.org/licenses/by/4.0/. The accompanying code is MIT-licensed.
\par\endgroup
```

# Introduction

Let $\xi(s)=\tfrac12 s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)$ and let $\lambda_n$ be the Li coefficients, defined by $\log\bigl(2\xi\bigl(\tfrac{1}{1-z}\bigr)\bigr)=\sum_{n\ge1}\lambda_n z^n/n$, with $\lambda_0=0$. Put
$$
c_n=\lambda_{n+1}-2\lambda_n+\lambda_{n-1}\qquad(n\ge1).
$$
This is Keiper's sequence $\tau_n$ [1, p. 769, eqs. (34) to (36)]; he shows that RH implies $|c_n|\le 2\lambda_1$ and that boundedness of $(c_n)$ implies RH. Li's criterion (RH holds if and only if $\lambda_n\ge0$ for all $n$) [8] (see [3, §1]) is not used below.

**What is known unconditionally.** In an earlier note [7] the author proves, with no hypothesis, that $c_n>0$ for infinitely many $n$ and $c_n<0$ for infinitely many $n$ (its Theorem 1), and, by a computer-assisted proof, that $c_1,\dots,c_{117}>0$ and $c_{118}<0$ (its Theorem 2). Xiao [2, Conjecture 3.4] conjectured that $\lambda_n>2\lambda_{n-1}-\lambda_{n-2}$ for all $n\ge3$, that is, $c_m>0$ for all $m\ge2$. Theorem 2 of [7] refutes this: the first failure is at $n=119$, since $c_{118}<0$. It says nothing about how long a run of one sign can be, or how often the sign changes. This paper studies both questions. Every new result is conditional.

**Zeros and angles.** Under RH write the zeros with positive ordinate as $\rho_k=\tfrac12+i\gamma_k$, $0<\gamma_1\le\gamma_2\le\cdots$, and put
$$
\theta_k=2\arctan\frac1{2\gamma_k},\qquad w_k=\frac1{\tfrac14+\gamma_k^2},\qquad C=2\lambda_1=2+\gamma_E-\log4\pi\approx0.0461914 .
$$

**Hypotheses.** We use the following.

- **RH.** Every nontrivial zero of $\zeta$ has real part $\tfrac12$.
- **LI$_\theta(K)$.** The numbers $\pi,\theta_1,\dots,\theta_K$ are linearly independent over $\mathbb{Q}$, where $\theta_1,\dots,\theta_K$ belong to the first $K$ ordinates (identified in Lemma \ref{lem:zeros}).
- **LI$_\theta$ (with multiplicity).** The numbers $\pi,\theta_1,\theta_2,\dots$, with $\theta_k$ listed with multiplicity (every copy of a multiple zero counted), are linearly independent over $\mathbb{Q}$. This forces every zero to be simple.

LI$_\theta$ is a hypothesis on the angles $\theta_k$. It is not the usual linear independence hypothesis on the ordinates $\gamma_k$, and we found no source that derives either from the other. It is open.

By a certificate we mean archived exact data (rationals or balls) together with a script that verifies the stated inequality in ball arithmetic with Arb [4].

**Results.** A run is a maximal block of consecutive indices $n\ge1$ with $c_n$ of one strict sign.

| Result | Statement | Hypotheses |
|-----------------|--------------------------------------|-----------------|
| Theorem A | every window of $1573$ consecutive $n$ has both signs; runs have length $\le1572$ | RH |
| Theorem B | runs of length at least $312$ of each sign, of positive lower density | RH |
| Theorem C | runs of $392$ (positive and negative) with lower density $\ge(r/\pi)^{700}$, $r\ge9.45\cdot10^{-4}$; runs of $476$ with $K=1400$ | RH and LI$_\theta(700)$; RH and LI$_\theta(1400)$ |
| Theorem D | density $\delta$ of sign changes exists; the ratio $\delta/(\theta_1/\pi)$ lies in $[0.969481285147,0.971027176735]$ | RH and LI$_\theta$ with multiplicity |
| Theorem D$'$ | same quantity for the truncated sequence $c^{(100)}_n$ | RH and LI$_\theta(100)$ |
| Searches, Monte Carlo, extrapolation | evidence only | none (numerical evidence only) |

**Remark.** On 20 November 2026 Alpöge [22] announced a proof of the Riemann hypothesis, together with a Lean 4 formalization of Mathlib's statement `RiemannHypothesis`. The Lean FRO and Mathlib Initiative [23] report that the formal proof was checked by the Lean kernel and by independent third-party checkers. As of 23 November 2026 no human-readable proof has been published, and the announcement has not been peer reviewed. If the proof is accepted, Theorems A and B hold without assuming RH. Theorems C, D and D$'$ would still need LI$_\theta(700)$ and LI$_\theta(1400)$, LI$_\theta$, and LI$_\theta(100)$ respectively, which the announced result does not supply.

Section 2 gives the zero formula and the zero list. Sections 3 to 6 prove the results; the longer proofs are in Appendix A, and Appendix B explains how to reproduce the certificates. Results that rest on a computer calculation say so in their statement; the files that verify them are listed in Appendix B.

Sources. Li [8] and Davenport [9] are cited through [3]; Lehman [10] and Brent [11] through the Arb documentation and [12]; Turing [20] and Rubinstein and Sarnak [13] are cited from secondary sources; for [17] to [19] we rely on the abstracts.

# The zero formula and the zero list

```{=latex}
\begin{lemma}\label{lem:formula}
```
Assume RH. For $n\ge1$,
$$
c_n=\sum_{\gamma>0}2m_\gamma w_\gamma\cos(n\theta_\gamma),\qquad \sum_{\gamma>0}2m_\gamma w_\gamma=C,
$$
where $\gamma$ runs over the ordinates of the zeros with $\gamma>0$ and $m_\gamma$ is the multiplicity. The series converges absolutely.

```{=latex}
\end{lemma}
```

<!-- statement
id: L1
label: CONDITIONAL
-->

```{=latex}
\begin{proof}
```
Li's formula $\lambda_n=\sum_\rho[1-(1-1/\rho)^n]$ [3, §1] gives $c_n=\sum_\rho w_\rho q_\rho^{\,n}$ with $q_\rho=1-1/\rho$ and $w_\rho=1/(\rho(1-\rho))$; for fixed $n$ the sum converges absolutely without RH [7, Remarks]. Under RH, $\rho=\tfrac12+i\gamma$ gives $w_\rho=1/(\tfrac14+\gamma^2)>0$ and $q_\rho=(-\tfrac12+i\gamma)/(\tfrac12+i\gamma)=e^{i\theta}$ with $\theta=\pi-2\arctan 2\gamma=2\arctan\frac1{2\gamma}$ for $\gamma>0$. Pairing $\rho$ with $\bar\rho$ gives the cosine. For the sum, $w_\rho=1/\rho+1/(1-\rho)$ and the zeros are symmetric under $\rho\mapsto1-\rho$, so $\sum_\rho w_\rho=2\sum_\rho1/\rho=2\lambda_1$, and $2\lambda_1=2+\gamma_E-\log4\pi$ by the closed form of $\lambda_1$ [3, Remark after Theorem 2], [9, pp. 83-84].
```{=latex}
\end{proof}
```

```{=latex}
\begin{lemma}[computer-assisted]\label{lem:zeros}
```
There are exactly $2000$ zeros of $\zeta$ with $0<\gamma\le T$, $T=2638142521/2^{20}\approx2515.93$. All lie on the critical line and all are simple. The ordinates $\gamma_1<\dots<\gamma_{2000}$ are enclosed by the balls in the certificate, with $\gamma_{2000}=2515.286\ldots$. The count rests on Arb's implementation of $N(T)$ being correct.

```{=latex}
\end{lemma}
```

<!-- statement
id: L2
label: PROVED
certificate: papers/keiper-li-sign-runs/code/z2000.json
-->

```{=latex}
\begin{proof}
```
Arb [4] isolates the first $2000$ zeros in ball arithmetic (python-flint $0.9.0$); the zeros are returned on the line and their count and order are checked. Independently of Arb's isolation, Hardy's function $Z$ has a certified sign change on $[\gamma-2^{-20},\gamma+2^{-20}]$ for each listed zero, and these intervals are disjoint. That gives at least $2000$ zeros of odd multiplicity on the line, in disjoint intervals. Arb's count of zeros up to $T$, with multiplicity, returns $2000$. This count uses Turing's method as made explicit by Lehman [10], Brent [11] and Trudgian [12, Thm 2.1 and Cor 2.3 of the arXiv version, arXiv:0903.1885] (a bound on the integral of $S(t)$), going back to Turing's method [20]. The Arb count is a computation that this paper trusts, not an independent certificate. So each of these zeros is simple and there are no others up to $T$.
```{=latex}
\end{proof}
```

Every theorem that uses the zero list inherits the assumption that Arb's count is correct.

# A window bound under RH

```{=latex}
\begin{theorem}[computer-assisted]\label{thm:A}
```
Assume RH. Every window of $1573$ consecutive indices $n\ge1$ contains an $n$ with $c_n>0$ and an $n$ with $c_n<0$. Hence every run of $c_n$ of one sign has length at most $1572$.

```{=latex}
\end{theorem}
```

<!-- statement
id: TA
label: CONDITIONAL
certificate: papers/keiper-li-sign-runs/code/cert_L1699.json, papers/keiper-li-sign-runs/code/cert_L1573.json, papers/keiper-li-sign-runs/code/z2000.json
-->

**Hypotheses:** RH. The zero list of Lemma \ref{lem:zeros} is used.

**Context.** Under RH some finite window bound follows from general facts about almost periodic sequences with mean zero; the contribution here is the explicit constant $1573$ with an exact certificate. Sketch of the soft bound (not used below): since $\sum_\rho w_\rho<\infty$ the series for $c_n$ converges uniformly, so $(c_n)$ is a Bohr almost periodic sequence, and its mean is $0$ because all $\theta_k\ne0$. If windows of one sign of every length existed, a limit of translates (an element of the hull) would be $\ge0$ (or $\le0$) with mean $0$, hence identically $0$, whereas every element of the hull has the same mean of $|c_n|$ as $c_n$, which is positive. Haraux [15, Thm 2.1] is only the continuous-time analogue: a real-valued almost periodic function with mean zero, not identically zero, takes both signs on every interval of some uniform length. It does not cover integer sampling or density.

```{=latex}
\begin{proof}
```
The proof combines Lemma \ref{lem:kernel} with a certified inequality (the certificate, detailed in Appendix A). Let $L\in\{1573,1699\}$ ($1573$ gives the theorem; $1699$ is also certified, with margin $5.92\%$), $L=2h+1$ ($h=786$ and $h=849$), and let $K_d=K_{-d}\ge0$ be the stored kernel (integer numerators over $2^{50}$). In ball arithmetic ($128$ bits, python-flint $0.9.0$) the inequality
$$
w_1\tilde k(0)>(\text{the three sums of Lemma \ref{lem:kernel} over the }2000\text{ listed zeros})+W\,\tilde k(0)(1+\mu_{\mathrm{arc}})
$$
holds, where $\mu_{\mathrm{arc}}$ is a certified upper bound for $\sup|\tilde k|/\tilde k(0)$ on the arc of the unlisted zeros (defined in Appendix A), with value $0.0027457$ for $L=1573$ and $0.0023355$ for $L=1699$, and $W=0.0008846762129$ (ball) is the weight of the unlisted zeros and $w_1=0.004998988834$. Write $R$ for the ratio of the right side to the left side. The certificate gives $R\le0.9983759146$ for $L=1573$ (margin $0.16\%$) and $R\le0.9407685236$ for $L=1699$ (margin $5.92\%$); both inequalities are verified rigorously, so the size of the margin plays no role. Now suppose a window $n_0,\dots,n_0+L-1$ with $n_0\ge1$ had $c_n\ge0$ throughout, or $c_n\le0$ throughout. Put $M=n_0+h\ge h+1$. By Lemma \ref{lem:kernel}, $w_1\tilde k(0)$ is at most the three sums over all zeros. The listed zeros contribute the same terms as in the certificate, and the unlisted zeros (all with $\gamma>T$, Lemma \ref{lem:zeros}) contribute at most $W\tilde k(0)(1+\mu_{\mathrm{arc}})$ (derivation in Appendix A). So $w_1\tilde k(0)\le R\,w_1\tilde k(0)<w_1\tilde k(0)$, a contradiction. Hence every window of $1573$ consecutive indices has $c_n<0$ for some $n$ and $c_n>0$ for some $n$. A run of one sign of length $1573$ would be such a window, so every run has length at most $1572$. The ratio is above $1$ for $L=1571$ ($1.0001440$) and $L=1551$ ($1.0148752$) (archived log), so $1573$ is the smallest length found for which this kernel certifies; it is not a limit of the method.
```{=latex}
\end{proof}
```

Figure \ref{fig:window} shows the certified ratio against $L$.

```{=latex}
\begin{figure}[H]\centering
\definecolor{fgblue}{RGB}{31,90,166}
\definecolor{fgred}{RGB}{190,40,40}
\begin{tikzpicture}
\begin{axis}[width=0.9\textwidth, height=6cm, xmin=1540, xmax=1710, ymin=0.93, ymax=1.02, xlabel={window length $L$}, ylabel={certified ratio},
  tick label style={font=\scriptsize}, label style={font=\small}, scaled y ticks=false, yticklabel style={/pgf/number format/fixed,/pgf/number format/precision=2}]
\addplot[domain=1540:1710,gray,thin,dashed] {1};
\addplot[thin,gray] table[header=false, skip first n=1, x index=0, y index=1] {data/fig1-window-ratio.dat};
\addplot[only marks,mark=*,mark size=1.4pt,fgblue] table[header=false, skip first n=1, x index=0, y index=1, restrict expr to domain={\thisrowno{2}}{1:1}] {data/fig1-window-ratio.dat};
\addplot[only marks,mark=*,mark size=1.4pt,fgred] table[header=false, skip first n=1, x index=0, y index=1, restrict expr to domain={\thisrowno{2}}{0:0}] {data/fig1-window-ratio.dat};
\node[font=\scriptsize,anchor=south west] at (axis cs:1576,1.003) {ratio $=1$};
\node[font=\scriptsize,fgblue,anchor=south east] at (axis cs:1708,0.958) {$L=1699$: $0.9408$};
\node[font=\scriptsize,fgblue,anchor=north west] at (axis cs:1573,0.975) {$L=1573$: $0.99838$};
\end{axis}
\end{tikzpicture}
\caption[Certified ratio against window length]{Theorem A. The certified upper bound of the ratio (right side over left side of the kernel inequality) against the window length $L$. Blue: ratio below $1$, so the window bound holds (under RH). Red: ratio not below $1$, so this kernel certifies nothing. The bound at $L=1573$ is the smallest length tried that certifies.}\label{fig:window}
\end{figure}
```

<!-- audio-description
Here in Figure {number} we see the certified ratio plotted against the window length L, from 1551 to 1699, with a dashed horizontal line at one. The points fall from 1.015 at L equal to 1551 to 0.94 at L equal to 1699. The ratio falls below one at L equal to 1573, where it is 0.998; below one means certified.
-->

# Runs of 312 values of both signs under RH

```{=latex}
\begin{theorem}[computer-assisted]\label{thm:B}
```
Assume RH. Let $N_+$ be the integer whose decimal digits are the file `witness_pos312.txt` ($1244$ digits, SHA-256 of the file \texttt{bb223123\allowbreak 9e1614f5\allowbreak 28ce2add\allowbreak 6478246f\allowbreak 720d7cd5\allowbreak 6c2d2cf9\allowbreak 83423254\allowbreak cb8c2b3e}), and $N_-$ the integer in `witness_neg312.txt` ($1243$ digits, SHA-256 of the file \texttt{33da2477\allowbreak 00995dc0\allowbreak aecaaf14\allowbreak 22b4ddd7\allowbreak 0438fe9a\allowbreak 7ba84539\allowbreak 26436366\allowbreak dc1f26b3}). Then $c_n>0$ for $N_+\le n\le N_++311$, and $c_n<0$ for $N_-\le n\le N_-+311$. Moreover the set of $M$ with $c_M,\dots,c_{M+311}$ all positive, and the set of $M$ with $c_M,\dots,c_{M+311}$ all negative, are syndetic (for some $Q$, they meet every block of $2Q+1$ consecutive integers from $N_\pm$ on), and so both have positive lower density. In particular there are infinitely many blocks of $312$ consecutive values of each sign.

```{=latex}
\end{theorem}
```

<!-- statement
id: TB
label: CONDITIONAL
certificate: papers/keiper-li-sign-runs/code/cert_witness_pos312.json, papers/keiper-li-sign-runs/code/cert_witness_neg312.json, papers/keiper-li-sign-runs/code/z2000.json
-->

**Hypotheses:** RH. No independence hypothesis is used. The zero list of Lemma \ref{lem:zeros} is used. The statement for $N_\pm$ itself is a finite computation (a certificate); the rest is a proof.

```{=latex}
\begin{proof}
```
In short: a finite computation shows that the sum over the first $300$ zeros has a margin over the tail bound on a window of $312$ at $N_\pm$; a shift by an integer that nearly fixes the phases of those $300$ zeros keeps the margin; and a compactness argument shows that such shifts occur in every block of bounded length.

*Setup.* Put $K=300$, $a_k=2w_k$, $F_K(m)=\sum_{k\le K}a_k\cos(m\theta_k)$ for every integer $m$, and $T_K=C-\sum_{k\le K}a_k$. For $\|t\|_{2\pi}$ the distance from a real $t$ to $2\pi\mathbb{Z}$, $|\cos(u+t)-\cos u|\le\|t\|_{2\pi}$ for all real $u$, since $\cos$ is $1$-Lipschitz and $2\pi$-periodic. By Lemma \ref{lem:zeros} the first $300$ zeros are distinct and simple, so Lemma \ref{lem:tail} (with all $x_k=0$) and Lemma \ref{lem:formula} give, for every integer $m\ge1$,
$$
|c_m-F_K(m)|\le T_K.
$$

*The certificate.* For $N=N_+$ and $0\le j\le311$ the certificate checks, in ball arithmetic, that $F_K(N+j)-T_K>0$; for $N=N_-$ it checks $-F_K(N+j)-T_K>0$. The precision is about $4300$ bits, so that $N\theta_k$ is evaluated with an error far below any margin. The $300$ zeros are recomputed at that precision and each is enclosed in a ball widened by $4$ ulps (units in the last place). $Z$ is checked to have opposite signs at the two ends of each ball, and the ball is checked to lie in the interval $[m-10^{-20},m+10^{-20}]$ about the midpoint $m$ of the same index in the archived list of the first $2000$ zeros, on whose two ends $Z$ has opposite signs (checked at $10^{-20}$ at the start of the run), so it encloses $\gamma_k$. The least values found are
$$
\begin{aligned}
\min_j\bigl(F_K(N_++j)-T_K\bigr)&\ge1.066\cdot10^{-4}\ (j=241),\\
\min_j\bigl(-F_K(N_-+j)-T_K\bigr)&\ge1.093\cdot10^{-4}\ (j=153),
\end{aligned}
$$
with $T_K<0.0031991$ and a ball radius below $10^{-61}$. Put $\varepsilon_0=10^{-4}$. So for both signs the margin over $T_K$ is at least $\varepsilon_0$ on the whole window.

*The margin gives the signs.* With the tail bound, $c_m\ge F_K(m)-T_K>0$ for $N_+\le m\le N_++311$, and $c_m\le F_K(m)+T_K<0$ for $N_-\le m\le N_-+311$. This is the first statement.

*Persistence.* For an integer $\ell$ put $D(\ell)=\sum_{k\le K}a_k\|\ell\theta_k\|_{2\pi}$. Then $D(-\ell)=D(\ell)$ and $D(\ell+\ell')\le D(\ell)+D(\ell')$. By the Lipschitz bound, $|F_K(m+\ell)-F_K(m)|\le D(\ell)$ for every integer $m$. Let $U=\{\ell\in\mathbb{Z}:D(\ell)<\varepsilon_0\}$. If $\ell\in U$, $\ell\ge0$, then for $0\le j\le311$ we get $F_K(N_++\ell+j)-T_K\ge F_K(N_++j)-T_K-D(\ell)>0$, so $c_{N_++\ell+j}>0$ by the tail bound; likewise $c_{N_-+\ell+j}<0$. Hence $N_++\ell$ is a start of a positive block of $312$, and $N_-+\ell$ of a negative one, for every $\ell\in U\cap[0,\infty)$.

*The set $U$ is syndetic.* Let $\mathbb{T}^K=(\mathbb{R}/2\pi\mathbb{Z})^K$, a compact group, and for $x\in\mathbb{T}^K$ put $\Delta(x)=\sum_{k\le K}a_k\|x_k\|_{2\pi}$. It is continuous, $\Delta(-x)=\Delta(x)$ and $\Delta(x+y)\le\Delta(x)+\Delta(y)$. With $\vartheta=(\theta_1,\dots,\theta_K)$, $D(\ell)=\Delta(\ell\vartheta)$. Let $\mathcal{H}$ be the closure of $\{\ell\vartheta:\ell\in\mathbb{Z}\}$; it is closed in a compact space, so compact. The open sets $\{x:\Delta(x-h)<\varepsilon_0/4\}$, $h\in\mathcal{H}$, cover $\mathcal{H}$, so finitely many of them, with centres $h_1,\dots,h_r\in\mathcal{H}$, do. Each $h_i$ lies in the closure of the orbit, so there is an integer $\ell_i$ with $\Delta(\ell_i\vartheta-h_i)<\varepsilon_0/4$. Let $\ell$ be any integer. Then $\ell\vartheta\in\mathcal{H}$ lies in one of the sets, say $\Delta(\ell\vartheta-h_i)<\varepsilon_0/4$, and
$$
D(\ell-\ell_i)=\Delta\bigl((\ell-\ell_i)\vartheta\bigr)\le\Delta(\ell\vartheta-h_i)+\Delta(h_i-\ell_i\vartheta)<\varepsilon_0/2,
$$
so $\ell-\ell_i\in U$. Put $Q=\max_i|\ell_i|$. Every integer $\ell$ therefore has an element of $U$ within distance $Q$. Apply this to $\ell=i(2Q+1)+Q$ for $i=0,1,2,\dots$: each block $\{i(2Q+1),\dots,i(2Q+1)+2Q\}$ of nonnegative integers contains an element of $U$. The same argument applies to every block $\{s,\dots,s+2Q\}$ with $s\ge0$, not only the aligned ones: take $\ell=s+Q$. So every block $\{s,\dots,s+2Q\}$ contains an element of $U$.

*Density.* Let $S_+$ be the set of $M\ge1$ with $c_M,\dots,c_{M+311}>0$. By the persistence step, $S_+\supseteq N_++(U\cap[0,\infty))$. The blocks above give at least $\lfloor(X-N_++1)/(2Q+1)\rfloor$ elements of $S_+$ in $[1,X]$, so $\liminf_{X\to\infty}\#(S_+\cap[1,X])/X\ge1/(2Q+1)>0$. The same holds for the set $S_-$ of starts of negative blocks, with the same $Q$.
```{=latex}
\end{proof}
```

**Remark 1 (the density constant).** The constant $1/(2Q+1)$ is not explicit. No independence hypothesis is assumed, so $\mathcal{H}$ is not known without an independence hypothesis, and the Haar measure of $\{\Delta<\varepsilon_0\}$ in $\mathcal{H}$ cannot be evaluated.

**Remark 2 (maximal runs).** By Theorem A every run has length at most $1572$. A maximal run of length $l\ge312$ contains at most $l-311\le1261$ elements of $S_+$ (starts of positive blocks of $312$), and every element of $S_+$ lies in such a run. So the starts of maximal positive runs of length at least $312$ have lower density at least $1/(1261(2Q+1))$, and the same holds for negative runs. In particular there are infinitely many maximal runs of length at least $312$ of each sign.

**The witnesses.** The integers $N_\pm$ were found by a lattice search in the manner of Odlyzko and te Riele [24], who used lattice reduction [25] to find integers at which the first zeros have nearly prescribed phases (for the Mertens conjecture). Here the first $300$ zeros are used, and the target phases for the negative run are those of the positive run shifted by $\pi$. The search is not part of the proof: the proof uses only the two integers and the certificate above, which is run independently of the search code.

**Earlier result.** Starting instead from the positivity of $c_1,\dots,c_{117}$ [7, Theorem 2] and the return of the phases of all zeros to $0$, the same persistence argument gives runs of $235$ positive values under RH; Theorem B gives a longer run, and for both signs.

# Recurring long runs under RH and independence

For phases $x\in(\mathbb{R}/2\pi\mathbb{Z})^K$ put $F_x(j)=\sum_{k\le K}2w_k\cos(j\theta_k+x_k)$ and $T_K=C-\sum_{k\le K}2w_k$.

```{=latex}
\begin{theorem}[computer-assisted]\label{thm:C}
```
Assume RH and LI$_\theta(700)$: $\pi,\theta_1,\dots,\theta_{700}$ are linearly independent over $\mathbb{Q}$. Then the set of $M$ with $c_M,\dots,c_{M+391}$ all positive has lower density at least $(r/\pi)^{700}$, where $r\ge9.45\cdot10^{-4}$; the same holds for runs of $392$ negative values. Assume instead RH and LI$_\theta(1400)$. Then runs of $476$ consecutive positive values, and of $476$ negative values, occur with lower density at least $(r/\pi)^{1400}$, $r\ge1.403\cdot10^{-3}$.

```{=latex}
\end{theorem}
```

<!-- statement
id: TC
label: CONDITIONAL
certificate: papers/keiper-li-sign-runs/code/cert_run_pos_K700.json, papers/keiper-li-sign-runs/code/cert_run_pos_K1400.json, papers/keiper-li-sign-runs/code/summary.json, papers/keiper-li-sign-runs/code/z2000.json
-->

**Size of the bound.** The bound is tiny (about $10^{-2465}$ for $K=700$); the point is that the density is positive.

**Hypotheses:** RH and LI$_\theta(700)$ for the first part; RH and LI$_\theta(1400)$ for the second. LI$_\theta$ is not the usual independence of the $\gamma_k$ (Section 1). The zero list of Lemma \ref{lem:zeros} is used.

```{=latex}
\begin{proof}
```
The phase vectors $x$ are stored in the certificates as exact dyadic rationals. For $K=700$ and $j=0,\dots,391$, ball arithmetic ($128$ bits) gives $m:=\min_jF_x(j)-T_K\ge4.192\cdot10^{-5}>0$, with the minimum at $j=145$ (Figure \ref{fig:run}). Lemma \ref{lem:tail} bounds the zeros beyond $K$ by $T_K$ uniformly in the phases, and Lemma \ref{lem:box} turns the margin into a box of radius $r=m/(2\sum_{k\le K}w_k)\ge9.45\cdot10^{-4}$. Lemma \ref{lem:weyl} gives the density. The negative run uses $x+\pi$, which turns $F_x$ into $-F_x$. For $K=1400$ the certificate gives $m\ge6.32\cdot10^{-5}$, $j=0,\dots,475$, minimum at $j=146$, and $r\ge1.403\cdot10^{-3}$.
```{=latex}
\end{proof}
```

**Remark.** Under RH alone, either the conclusion of Theorem C holds for $K=700$, or $\pi,\theta_1,\dots,\theta_{700}$ satisfy a nontrivial rational relation; in the second case the orbit closure of the phases is a proper closed subgroup, which may or may not meet the box. Under RH alone the longest runs proved here are those of Theorem B, which need an explicit witness; a witness for a longer row of Figure \ref{fig:runs} would give a longer run, but we have not found one.

**The phase search.** The phases come from a floating point search over the torus (sequential linear programming; search code archived with the paper, Appendix B; not part of the certificate). For each $K$ in $100,150,200,250,300,400,500,700,1000,1400$ it finds phases with a run of the longest length $L(K)$ for which the margin over $T_K$ is positive in floating point, and the certificate then confirms each row in ball arithmetic. The values $L(K)$ are lower bounds of the torus supremum (the largest run attainable over all phase choices on the torus); the search does not show that longer runs are impossible. Rows other than $K=700$ and $K=1400$ are not stated as theorems here, though each is certified in the same way under LI$_\theta(K)$ (the archived summary, Appendix B). Figure \ref{fig:runs} shows the rise from $208$ at $K=100$ to $476$ at $K=1400$.

```{=latex}
\begin{figure}[H]\centering
\definecolor{fgblue}{RGB}{31,90,166}
\definecolor{fgred}{RGB}{190,40,40}
\begin{tikzpicture}
\begin{axis}[width=0.92\textwidth, height=6.4cm, xmin=0, xmax=1500, ymin=150, ymax=1750, xlabel={number of zeros $K$}, ylabel={run length},
  tick label style={font=\scriptsize}, label style={font=\small}, scaled y ticks=false]
\addplot[domain=0:1500,fgred,dashed] {1572};
\addplot[domain=0:1500,gray,dashed] {312};
\addplot[only marks,mark=*,mark size=1.5pt,fgblue] table[header=false, skip first n=1, x index=0, y index=1] {data/fig2-run-length.dat};
\addplot[only marks,mark=o,mark size=1.5pt,gray] table[header=false, skip first n=1, x index=0, y index=3] {data/fig2-run-length.dat};
\node[font=\scriptsize,fgred,anchor=north east] at (axis cs:1490,1560) {$1572$: Theorem A, RH (upper bound for every run)};
\node[font=\scriptsize,gray,anchor=north east,inner sep=2pt] at (axis cs:1490,300) {$312$: Theorem B, RH};
\node[font=\scriptsize,fgblue,anchor=south east] at (axis cs:1490,500) {$476$ at $K=1400$};
\end{axis}
\end{tikzpicture}
\caption[Run length against the number of zeros]{Run lengths against the number of zeros $K$. Blue dots: certified run length $L(K)$ of the run with margin over $T_K$; the rows $K=700$ ($392$) and $K=1400$ ($476$) are the two cases of Theorem C, each under RH and LI$_\theta(K)$; the other blue dots are certified the same way but not stated as theorems. They are lower bounds of the torus supremum, found by a numerical search. Open circles: the longest run of the $K$-term model without the tail allowance (search value, floating point). Dashed lines: $312$ (Theorem B, RH) and $1572$ (Theorem A, RH).}\label{fig:runs}
\end{figure}
```

<!-- audio-description
Here in Figure {number} we see run length plotted against the number of zeros K, from 100 to 1400. Blue dots rise from 208 at K equal to 100 to 476 at K equal to 1400, with 392 at K equal to 700. A grey dashed line at 312 touches the blue dot at K equal to 300, lies above the dots for smaller K and below the dots for larger K, and a red dashed line at 1572 lies far above all of them; the gap between 476 and 1572 is the open range.
-->

```{=latex}
\begin{figure}[H]\centering
\definecolor{fgblue}{RGB}{31,90,166}
\definecolor{fgred}{RGB}{190,40,40}
\begin{tikzpicture}
\begin{axis}[width=0.92\textwidth, height=6cm, xmin=-5, xmax=400, ymin=-0.004, ymax=0.034, xlabel={$j$}, ylabel={$F_x(j)$},
  tick label style={font=\scriptsize}, label style={font=\small}, scaled y ticks=false, yticklabel style={/pgf/number format/fixed,/pgf/number format/precision=3}]
\addplot[thick,fgblue] table[header=false, skip first n=1, x index=0, y index=1] {data/fig3-run-K700.dat};
\addplot[thick,fgred,dashed] table[header=false, skip first n=1, x index=0, y index=2] {data/fig3-run-K700.dat};
\addplot[only marks,mark=o,mark size=2.6pt,fgred,thick] coordinates {(145,0.00188)};
\draw[fgred,thin] (axis cs:145,0.0045) -- (axis cs:145,0.0265);
\node[font=\scriptsize,fgred,anchor=south] at (axis cs:145,0.0265) {closest approach at $j=145$, margin $4.2\cdot10^{-5}$};
\node[font=\scriptsize,fgred,anchor=north west] at (axis cs:210,0.0005) {threshold $T_{700}$};
\end{axis}
\end{tikzpicture}
\caption[The certified run at $K=700$]{The run of Theorem C for $K=700$: $F_x(j)=\sum_{k\le700}2w_k\cos(j\theta_k+x_k)$ for $j=0,\dots,391$ (blue) and the threshold $T_{700}=C-\sum_{k\le700}2w_k\approx1.835\cdot10^{-3}$ (red, dashed). The curve is plotted in double precision; the certified quantity is the minimum margin over $T_{700}$, computed in ball arithmetic, and it is positive. The curve exceeds the threshold at every $j$; under RH and LI$_\theta(700)$, Theorem C turns this into runs of $c_n$.}\label{fig:run}
\end{figure}
```

<!-- audio-description
Here in Figure {number} we see a blue curve for j from 0 to 391 that rises from about 0.0019 at j equal to 0 and wiggles between small and larger positive values, always above a dashed red line at 0.0018. The closest approach to the dashed line is circled at j equal to 145, with margin 4.2 times ten to the minus five.
-->

# The density of sign changes

Let $\delta$ be the density of $n$ with $c_nc_{n+1}<0$, when it exists. The quantity to compare with is $\theta_1/\pi=0.0225103222285$, the density of sign changes of $\cos(n\theta_1)$ alone.

Let $X=(X_k)$ be Haar distributed on the torus $\mathbb{T}^{\infty}=(\mathbb{R}/2\pi\mathbb{Z})^{\mathbb{N}}$, and put $F(x)=\sum_k a_k\cos x_k$ with $a_k=2w_k$ (all zeros are simple under LI$_\theta$).

```{=latex}
\begin{theorem}[computer-assisted]\label{thm:D}
```
Assume RH and LI$_\theta$ with multiplicity: $\pi,\theta_1,\theta_2,\dots$, with $\theta_k$ listed with multiplicity, are linearly independent over $\mathbb{Q}$. Then the density $\delta$ of sign changes of $c_n$ exists, equals $\mathbb{P}\bigl(F(X)F(X+\Theta)<0\bigr)$, and
$$
0.969481285147\ \le\ \frac{\delta}{\theta_1/\pi}\ \le\ 0.971027176735 .
$$
In particular $\delta<\theta_1/\pi$.

```{=latex}
\end{theorem}
```

<!-- statement
id: TD
label: CONDITIONAL
certificate: papers/keiper-li-sign-runs/code/density_results.json, papers/keiper-li-sign-runs/code/z2000.json
-->

**Hypotheses:** RH and LI$_\theta$ with multiplicity. The zero list of Lemma \ref{lem:zeros} is used. LI$_\theta$ differs from the usual independence of the $\gamma_k$ (Section 1), is unproved, and forces all zeros to be simple.

```{=latex}
\begin{proof}
```
Lemma \ref{lem:density} gives existence and the formula, Lemma \ref{lem:lattice} expresses $\delta$ as an exact lattice sum, and Lemmas \ref{lem:bessel} and \ref{lem:beyond} bound the effect of the zeros beyond the first $100$. The lattice sum is evaluated in ball arithmetic ($128$ bits, the half box $j\ge0$, $489258$ lattice points) with the box-tail Lemma \ref{lem:boxtail}; the result is the stated bracket (width $0.155\%$).
```{=latex}
\end{proof}
```

```{=latex}
\begingroup\renewcommand{\thetheorem}{D$'$}\begin{theorem}[computer-assisted]
```
Assume RH and LI$_\theta(100)$. For the truncated sequence $c^{(100)}_n=\sum_{k\le100}2w_k\cos(n\theta_k)$, the density $\delta_{100}$ of its sign changes exists and
$$
0.970254230937\ \le\ \frac{\delta_{100}}{\theta_1/\pi}\ \le\ 0.970254230944 .
$$
This is a statement about the model $c^{(100)}_n$, not about $c_n$.

```{=latex}
\end{theorem}\endgroup
```

<!-- statement
id: TD2
label: CONDITIONAL
certificate: papers/keiper-li-sign-runs/code/density_results.json, papers/keiper-li-sign-runs/code/z2000.json
-->

**Hypotheses:** RH (for the zero list and weights) and LI$_\theta(100)$. The zero list of Lemma \ref{lem:zeros} is used.

```{=latex}
\begin{proof}
```
The proof is that of Theorem D with the tail zeros removed: Lemma \ref{lem:density} for the $100$-term model (the same proof, with Weyl [6] on the $100$-torus under LI$_\theta(100)$, gives existence and the Haar formula for $c^{(100)}_n$) and Lemma \ref{lem:lattice}, and the certified lattice sum. Lemmas \ref{lem:bessel} and \ref{lem:beyond} are not needed.
```{=latex}
\end{proof}
```

**Remark on the moment bound.** The cruder bound $\sum_{k>2000}a_k^2\le T_{2000}^2$ gives a bracket of width $2.07\%$. Lemma \ref{lem:beyond} sharpens it to width $0.155\%$, at the cost of needing every zero to be simple; this is why LI$_\theta$ is stated with multiplicity.

**Monte Carlo and the effect of more zeros (numerical).** For the $K$-term model, the same Fourier method gives $\delta_K/(\theta_1/\pi)=0.971504,\,0.970254,\,0.970126,\,0.970112$ for $K=30,100,300,1000$, the differences falling by about a factor $10$ per factor $3.2$ in $K$. A Monte Carlo run with $10^7$ samples at $K=100$ gives $0.96945\pm0.00205$, consistent with the Fourier value. Extrapolating the differences to $K\to\infty$ gives about $0.97011$, with a band $[0.96975,0.97036]$. The extrapolation is a heuristic, not a proof; the proved bracket for the full sequence is that of Theorem D.

Figure \ref{fig:density} collects these values.

**Johansson's table (numerical, finite range).** Sign changes of $c_n$ were counted from Johansson's table [21] of $\lambda_n$ up to $n=10^5$ (20 significant digits; no sign is uncertain under worst-case rounding, bounding each rounding error by half a unit in the last place). Let $S(N)$ be the number of $n\in[2,N]$ with $c_n$ and $c_{n-1}$ of opposite sign. For $N=99999$, $S=2173$, and the ratio of $S$ to $\theta_1N/\pi$ is $0.9653$. Over the second half $n\in[N/2,N]$ of the range the ratios are $1.066$ ($N=1000$), $1.007$ ($N=3000$), $1.004$ ($N=10^4$), $0.974$ ($N=3\cdot10^4$) and $0.952$ ($N=99999$). The ratio over the whole range lies below the bracket of Theorem D, $[0.96948,0.97103]$. A finite range need not match the limiting density, and the second-half ratios move on both sides of the bracket. This is an illustration, not evidence for or against Theorem D. The counts are archived with the paper (Appendix B); the table itself is not.

```{=latex}
\begin{figure}[H]\centering
\definecolor{fgblue}{RGB}{31,90,166}
\definecolor{fgred}{RGB}{190,40,40}
\definecolor{fggreen}{RGB}{20,125,70}
\begin{tikzpicture}
\begin{axis}[width=0.8\textwidth, height=6.4cm, xmin=0.9665, xmax=0.9725, ymin=-0.7, ymax=7.7, xlabel={$\delta/(\theta_1/\pi)$},
  ytick={0,1,2,3,4,5,6,7}, yticklabels={Theorem D,Theorem D$'$ (K=100 model),K=100 Fourier,K=30,K=300,K=1000,Monte Carlo K=100,K to infinity (heuristic)},
  tick label style={font=\scriptsize}, label style={font=\small}, scaled x ticks=false, xtick={0.967,0.968,0.969,0.970,0.971,0.972}, xticklabel style={/pgf/number format/fixed,/pgf/number format/precision=3}]
\addplot[only marks,mark=square*,mark size=2pt,fgblue,error bars/.cd,x dir=both,x explicit] table[header=false, skip first n=1, x index=4, y expr=\coordindex, x error expr=\thisrowno{3}-\thisrowno{4}, restrict y to domain=0:0] {data/fig4-density.dat};
\addplot[only marks,mark=diamond*,mark size=3.2pt,fggreen,error bars/.cd,x dir=both,x explicit] table[header=false, skip first n=1, x index=4, y expr=\coordindex, x error expr=\thisrowno{3}-\thisrowno{4}, restrict y to domain=1:1] {data/fig4-density.dat};
\node[font=\scriptsize,fggreen,anchor=west] at (axis cs:0.9712,1) {width $7\cdot10^{-12}$};
\addplot[only marks,mark=o,mark size=2pt,fgred,error bars/.cd,x dir=both,x explicit] table[header=false, skip first n=1, x index=4, y expr=\coordindex, x error expr=\thisrowno{3}-\thisrowno{4}, restrict y to domain=2:6] {data/fig4-density.dat};
\addplot[only marks,mark=triangle,mark size=2.4pt,gray,error bars/.cd,x dir=both,x explicit] table[header=false, skip first n=1, x index=4, y expr=\coordindex, x error expr=\thisrowno{3}-\thisrowno{4}, restrict y to domain=7:7] {data/fig4-density.dat};
\end{axis}
\end{tikzpicture}
\caption[Density bracket]{The density ratio $\delta/(\theta_1/\pi)$. Filled markers with bars: the proved bracket of Theorem D (blue square, under RH and LI$_\theta$, with multiplicity) and of Theorem D$'$ (green diamond, under RH and LI$_\theta(100)$). The bracket of Theorem D$'$ has width about $7\cdot10^{-12}$, too narrow to see, and is a statement about the truncated sequence $c^{(100)}_n$ only, not about $c_n$. Open circles: values for the $K$-term model by the same method, and a Monte Carlo estimate with its standard error (numerical). Triangle: the extrapolation to $K\to\infty$ with its band (heuristic, no proof). Every value is below $1$.}\label{fig:density}
\end{figure}
```

<!-- audio-description
Here in Figure {number} we see eight horizontal marks, one per row, along an axis for the ratio of the sign-change density to theta one over pi, from 0.9665 to 0.9725. The proved bracket of Theorem D, from 0.96948 to 0.97103, is a filled square with a bar at the top row. Theorem D prime is a point at 0.97025, and the other rows scatter between 0.9674 and 0.9715 around it. Every mark is below one.
-->

# Remarks

**The gap.** Under RH, runs of one sign have length at most $1572$ (Theorem A), and runs of $312$ values of each sign recur (Theorem B). Under RH and LI$_\theta(1400)$, runs of $476$ recur (Theorem C). We do not know the true maximal run length. A possible route to Theorem C without LI$_\theta$ is an explicit Kronecker-Weyl theorem that needs no independence hypothesis, as in Bailleul [19] (we have not pursued this). More zeros, or a kernel that tests two zeros at once, might lower the window bound below $1573$ (we have not tried this).

**What the density says.** Under the hypotheses of Theorem D, the sign changes are slightly rarer than the $\theta_1/\pi\approx1/44.4$ of the lowest frequency alone, by about $3\%$.

**Status of LI$_\theta$.** Hypotheses of this kind appear in work on prime number races and Chebyshev's bias [13, 14], where the independence concerns the $\gamma_k$ themselves (see [14, §1 and §2]). Those papers are not used in any proof here. We do not claim any relation between the two hypotheses.

**Prior art.** The search of the note [7] (see [7] for the sources examined) found no result on the sign pattern of $c_n$ beyond Keiper's bound [1] and Xiao's conjecture [2], refuted in [7]; for this paper we found none that bounds runs of $c_n$ or computes the density of its sign changes, to our knowledge. We make no claim of novelty for the method: a torus model of an almost periodic sum, Weyl equidistribution, and a Fourier computation are classical in spirit, and Feuerverger and Martin [14] compute such densities numerically, with stated error estimates, under the generalized Riemann hypothesis (GRH) and the linear independence of the ordinates $\gamma_k$ (LI, the plain independence over $\mathbb{Q}$, unlike $\mathrm{LI}_\theta$ above). We found no Kac-Rice result for sampled sequences. The continuous-time analogue of a bounded run length is Haraux [15, Thm 2.1], see Theorem A. For the sign changes of $\psi(x)-x$ ($\psi$ the Chebyshev function), a zero sum with a rate above the lowest frequency, see [17, 18]: Grześkowiak, Kaczorowski, Pańkowski and Radziejewski show, with $\gamma_1$ the first ordinate, $\liminf V(T)/\log T\ge\gamma_1/\pi+1/60$ for the number $V(T)$ of sign changes of $\psi(x)-x$ up to $T$, and Morrill, Platt and Trudgian give a bound of the same form. The setting there is continuous and the rate is above the lowest frequency; here it is a discrete sequence and the rate found is below it. We claim no novelty for the method of Theorem B. The search for long runs is the scheme Odlyzko and te Riele [24] used to disprove the Mertens conjecture: LLL reduction [25] finds an integer at which the first zeros have nearly prescribed phases, and a certified evaluation with a bound on the remaining zeros turns it into a witness. To our knowledge it has not been applied to the Keiper-Li coefficients, and we found no earlier bound on the length of sign runs of $c_n$.


# Code and data {-}

The code, the zero list and all certificate files are public at <https://github.com/mik-tf/keiper-li-sign-runs> and will be archived on Zenodo. Appendix B explains how to reproduce each certificate; the search code that found the witnesses of Theorem B and the phases of Theorem C is archived with it (Appendix B), and it is not part of any proof.

# Use of AI {-}

Claude Opus 5.5 and Claude Sonnet 5.5 (Anthropic) were used in November 2026 for exploratory computation, in which the main results were first found, for the lattice search and the certificate for Theorem B, and for checking, literature search and drafting.

# Appendix A: proofs {-}

Throughout, RH holds, $\theta_k,w_k,C$ are as in Section 1, and sums over zeros count multiplicity.

```{=latex}
\begin{lemma}[kernel inequality]\label{lem:kernel}
```
Assume RH. Let $h\ge1$, $K_d=K_{-d}\ge0$ for $|d|\le h$, $\tilde k(\varphi)=\sum_{|d|\le h}K_de^{id\varphi}$ (real, even), and $M\ge h+1$. If $c_n\ge0$ for $|n-M|\le h$, or $c_n\le0$ for $|n-M|\le h$, then, with $\rho_1$ the first zero (simple, Lemma \ref{lem:zeros}),
$$
w_1\tilde k(0)\le\sum_{\gamma>0}2m_\gamma w_\gamma|\tilde k(\theta_\gamma)|+\sum_{\gamma>0,\ \gamma\ne\gamma_1}m_\gamma w_\gamma|\tilde k(\theta_\gamma-\theta_1)|+\sum_{\gamma>0}m_\gamma w_\gamma|\tilde k(\theta_\gamma+\theta_1)|.
$$

```{=latex}
\end{lemma}
```

<!-- statement
id: AL1
label: CONDITIONAL
-->

**Hypotheses:** RH.

```{=latex}
\begin{proof}
```
Take $c_n\ge0$ (the other case is the same with $-c_n$). By Lemma \ref{lem:formula}, $c_n=\sum_{\gamma>0}m_\gamma w_\gamma(e^{in\theta_\gamma}+e^{-in\theta_\gamma})$. Put $S=\sum_dK_dc_{M+d}e^{i(M+d)\theta_1}$. Then
$$
S=\sum_{\gamma>0}m_\gamma w_\gamma\bigl[e^{iM(\theta_\gamma+\theta_1)}\tilde k(\theta_\gamma+\theta_1)+e^{iM(\theta_1-\theta_\gamma)}\tilde k(\theta_1-\theta_\gamma)\bigr].
$$
The term $\gamma=\gamma_1$ of the second kind is $w_1\tilde k(0)$, of modulus $w_1\tilde k(0)$, so $|S|\ge w_1\tilde k(0)-(\text{the other two sums})$. Since $K_d\ge0$ and $c_{M+d}\ge0$, $|S|\le\sum_dK_dc_{M+d}=\sum_{\gamma>0}2m_\gamma w_\gamma\cos(M\theta_\gamma)\tilde k(\theta_\gamma)\le\sum2m_\gamma w_\gamma|\tilde k(\theta_\gamma)|$. Combining the two bounds gives the inequality.
```{=latex}
\end{proof}
```

**The inequality verified for Theorem A.** The certificate verifies, in ball arithmetic, that
$$
w_1\tilde k(0)>2\sum_{k\le2000}w_k|\tilde k(\theta_k)|+\sum_{2\le k\le2000}w_k|\tilde k(\theta_k-\theta_1)|+\sum_{k\le2000}w_k|\tilde k(\theta_k+\theta_1)|+W\,\tilde k(0)(1+\mu_{\mathrm{arc}})
$$
for the stored integer kernel, where $W=C-2\sum_{k\le2000}w_k$ is the total weight $2\sum m w$ of the zeros above $T$ (an identity by Lemmas \ref{lem:formula} and \ref{lem:zeros}), and $\mu_{\mathrm{arc}}\ge\sup|\tilde k|/\tilde k(0)$ on the arc $[-\theta_T-\theta_1,\theta_T-\theta_1]$, $\theta_T=2\arctan\frac1{2T}$, which contains $\theta_\gamma-\theta_1$ and, by evenness, $-(\theta_\gamma+\theta_1)$ for every unlisted $\gamma$. For unlisted zeros, $|\tilde k|\le\tilde k(0)$ (as $K_d\ge0$) bounds the first sum by $W\tilde k(0)$, and the other two by $\tfrac{W}{2}\mu_{\mathrm{arc}}\tilde k(0)$ each. The bound $\mu_{\mathrm{arc}}$ comes from a grid of arc centres (spacing about $5\cdot10^{-6}$) plus the Lipschitz estimate $|\tilde k'|\le h\tilde k(0)$, so $\sup$ over a cell is at most the value at its centre plus $h\cdot(\text{cell radius})\cdot\tilde k(0)$. The inequality contradicts Lemma \ref{lem:kernel}, so no window has a one-signed $c_n$. The kernel was found by linear programming in floating point, then rounded to integers over $2^{50}$; only the exact rationals enter the certificate.

```{=latex}
\begin{lemma}[tail, uniform in phases]\label{lem:tail}
```
Assume RH, and that $\theta_1,\dots,\theta_K$ belong to $K$ distinct simple zeros. Then for every real phase $x_\gamma$ and every integer $n$, $\bigl|\sum_{\gamma\text{ not among these }K\text{ zeros}}2m_\gamma w_\gamma\cos(n\theta_\gamma+x_\gamma)\bigr|\le T_K=C-\sum_{k\le K}2w_k$.

```{=latex}
\end{lemma}
```

<!-- statement
id: AL2
label: CONDITIONAL
-->

**Hypotheses:** RH.

```{=latex}
\begin{proof}
```
Each term has modulus at most $2m_\gamma w_\gamma$, and $\sum_{\gamma>0}2m_\gamma w_\gamma=C$ (Lemma \ref{lem:formula}). The $K$ listed zeros carry $\sum_{k\le K}2w_k$ of it, so the rest carries $T_K$. A missing zero would only move weight into the tail; the listed zeros must be distinct.
```{=latex}
\end{proof}
```

```{=latex}
\begin{lemma}[Lipschitz box]\label{lem:box}
```
For $x,x'\in\mathbb{R}^K$ and every $j$, $|F_{x'}(j)-F_x(j)|\le\sum_k2w_k|x'_k-x_k|$. Hence if $F_x(j)\ge T_K+m$ for $0\le j<L$, then $F_{x'}(j)>T_K$ for all such $j$ whenever $\|x'-x\|_\infty<r:=m/(2\sum_{k\le K}w_k)$.

```{=latex}
\end{lemma}
```

<!-- statement
id: AL3
label: PROVED
-->

```{=latex}
\begin{proof}
```
$|\cos a-\cos b|\le|a-b|$.
```{=latex}
\end{proof}
```

```{=latex}
\begin{lemma}[transfer by equidistribution]\label{lem:weyl}
```
Assume RH and LI$_\theta(K)$. Let $B\subset(\mathbb{R}/2\pi\mathbb{Z})^K$ be an open box of side $2r$ about $x$, with $F_{x'}(j)>T_K$ for $0\le j<L$ and all $x'\in B$. Then the set of $M\ge1$ with $c_{M+j}>0$ for $0\le j<L$ has lower density at least $(r/\pi)^K$.

```{=latex}
\end{lemma}
```

<!-- statement
id: AL4
label: CONDITIONAL
-->

**Hypotheses:** RH and LI$_\theta(K)$.

```{=latex}
\begin{proof}
```
Because $\pi,\theta_1,\dots,\theta_K$ are independent over $\mathbb{Q}$, the sequence $(M\theta_1,\dots,M\theta_K)$ mod $2\pi$ is equidistributed on the $K$-torus (Weyl [6, Satz 4, p. 319, via Satz 3 and Satz 1]). A box is a continuity set, so Weyl's theorem gives the density of $\{M:M\theta\in B\}$ directly, and it equals the Haar measure of $B$, which is $(2r/2\pi)^K=(r/\pi)^K$. For such $M$, $c_{M+j}=F_{M\theta}(j)+\epsilon$ with $|\epsilon|\le T_K$ by Lemma \ref{lem:formula} and Lemma \ref{lem:tail}, and $F_{M\theta}(j)>T_K$, so $c_{M+j}>0$.
```{=latex}
\end{proof}
```

**Density.** Write $\mathbb{T}^\infty$ as above and let $\Theta=(\theta_k)$ act by translation. Let $\omega_k=s+t(e^{i\theta_k}-1)$, and let $\varphi(s,t)=\prod_kJ_0(a_k|\omega_k|)$.

```{=latex}
\begin{lemma}[existence and the Haar formula]\label{lem:density}
```
Assume RH and LI$_\theta$ with multiplicity. Then every zero is simple, $c_n=F(n\Theta)$ for $n\ge1$, and the density of $n$ with $c_nc_{n+1}<0$ exists and equals $\mathbb{P}(F(X)F(X+\Theta)<0)=2\,\mathbb{P}\bigl((F(X),D)\in T_1\bigr)$, where $D=F(X+\Theta)-F(X)$ and $T_1=\{(u,d):0<u<-d\}$.

```{=latex}
\end{lemma}
```

<!-- statement
id: AL5
label: CONDITIONAL
-->

**Hypotheses:** RH and LI$_\theta$ with multiplicity.

```{=latex}
\begin{proof}
```
A multiple zero would repeat an angle, giving a rational relation, so all zeros are simple and $c_n=F(n\Theta)$ by Lemma \ref{lem:formula}. By Weyl [6] on every finite set of coordinates, and approximation of continuous functions on $\mathbb{T}^\infty$ (continuity of $F$ follows from $\sum a_k<\infty$), $(n\Theta)_n$ is equidistributed for the Haar measure. The indicator $H=\mathbf 1\{F(x)F(x+\Theta)<0\}$ is continuous off $\{F(x)=0\}\cup\{F(x+\Theta)=0\}$. For fixed values of the other coordinates, each set contains at most two values of $x_1$, so both are Haar-null by Fubini. The empirical measures of $(n\Theta)$ converge weakly to the Haar measure, and $H$ is bounded with a Haar-null set of discontinuities. By the portmanteau theorem (a standard fact: weak convergence of probability measures on a compact metric space implies convergence of the integrals of every bounded function whose discontinuity set is null for the limit), the average of $H(n\Theta)$ tends to $\mathbb{E}H$. For the second equality, $x\mapsto x+\pi$ (all coordinates) sends $(F,F(\cdot+\Theta))$ to its negative, so $\mathbb{P}(F_0F_1<0)=2\mathbb{P}(F_0>0>F_1)$, and $F_0>0>F_0+D$ means $0<F_0<-D$.
```{=latex}
\end{proof}
```

By Bessel's integral [16, (10.9.1)], $J_0(x)=\frac1\pi\int_0^\pi\cos(x\sin u)\,du$, $\mathbb{E}\,e^{ia\,\mathrm{Re}(\omega e^{iX})}=J_0(a|\omega|)$ for $X$ uniform. Since $sF+tD=\sum_ka_k\,\mathrm{Re}(\omega_ke^{iX_k})$ with independent coordinates, the characteristic function of $(F(X),D)$ is $\varphi$. The pair has compact support: $|F|\le C$ and $|D|\le S_d$, where $S_d=\sum_k2a_k\sin(\theta_k/2)\le \beta$, $\beta=1529/2^{20}$ (certified upper bound). For the zeros beyond the first $2000$, $2a\sin(\theta/2)\le a\theta\le a/\gamma_{2000}$ and their $a$ sum to $T_{2000}=C-\sum_{k\le2000}a_k$, so the computation adds $T_{2000}/\gamma_{2000}$ to the sum over the listed zeros (ball arithmetic, upper end).

```{=latex}
\begin{lemma}[lattice identity]\label{lem:lattice}
```
Let $T_1^\beta=\{(u,d):0<u<-d<\beta\}$ and $\widehat{\mathbf 1_{T_1^\beta}}(\sigma,\tau)=\int_{T_1^\beta}e^{i(\sigma u+\tau d)}\,du\,dd$ (Fourier sign convention $e^{+i\langle\xi,\cdot\rangle}$, the same as for $\varphi(s,t)=\mathbb{E}\,e^{i(sF+tD)}$). With $u=Lx$, $d=-Ly$,
$$
\begin{aligned}
\widehat{\mathbf 1_{T_1^\beta}}(\sigma,\tau)&=\beta^2\int_{0<x<y<1}e^{i\sigma Lx-i\tau Ly}\,dx\,dy=\beta^2\,\frac{E(\sigma \beta-\tau \beta)-E(-\tau \beta)}{i\sigma \beta},\\
E(z)&=\frac{e^{iz}-1}{iz},\ E(0)=1,
\end{aligned}
$$
and the cases $\sigma=0$ are the limits (for $\sigma=0$, $\tau\ne0$: $\beta^2[e^{-i\tau \beta}(1+i\tau \beta)-1]/(\tau \beta)^2$; for $\sigma=\tau=0$: $\beta^2/2$). Let $h_s,h_t>0$ with $2\pi/h_s>C+\beta$ and $2\pi/h_t>2\beta$, where $\beta\ge S_d$ (certified values $\beta=1529/2^{20}$, $h_s=67513/1024$, $h_t=1103093/1024$). Then
$$
\mathbb{P}\bigl((F,D)\in T_1\bigr)=\frac{h_sh_t}{4\pi^2}\sum_{(s,t)\in h_s\mathbb{Z}\times h_t\mathbb{Z}}\varphi(s,t)\,\mathrm{Re}\,\widehat{\mathbf 1_{T_1^\beta}}(s,t).
$$
(Here $T_1$ may be replaced by $T_1^\beta$: $D\ge-S_d>-\beta$ always, since $S_d<\beta$ for the certified $\beta$.)

```{=latex}
\end{lemma}
```

<!-- statement
id: AL6
label: CONDITIONAL
-->

**Hypotheses:** RH and LI$_\theta$ with multiplicity (for the full model); the same lemma holds for the truncated model under LI$_\theta(100)$.

```{=latex}
\begin{proof}
```
Let $\mu$ be the law of $(F,D)$ (or of the $100$-term model $(F_{100},D_{100})$) and $T=T_1^\beta$.

(i) Density. $|\varphi|\le|\varphi_{100}|$ because every Bessel factor lies in $[-1,1]$, and $\varphi_{100}\in L^1(\mathbb{R}^2)$ by Lemma \ref{lem:boxtail}(a) (decay of order $\nu^{-19.5}$ off the box, bounded by $1$ inside). By Fourier inversion $\mu$ has a bounded continuous density $f$, supported in $[-C,C]\times[-S_d,S_d]$, for both models.

(ii) Continuity. Put $G(v)=\mu(T-v)=\int f(y-v)\mathbf 1_T(y)\,dy$. Since $f$ is bounded, continuous and compactly supported, $G$ is continuous (dominated convergence), and $G(0)=\mathbb{P}((F,D)\in T)$.

(iii) Support. $G(v)\ne0$ forces $v=y-x$ with $y\in T$ and $x\in\mathrm{supp}f$, so $v_1\in(-C,\beta+C)$ and $v_2\in(-\beta-S_d,S_d)$.

(iv) Fourier transform. With $y=x+v$, $\widehat G(\xi)=\int G(v)e^{i\langle\xi,v\rangle}dv=\widehat{\mathbf 1_T}(\xi)\int f(x)e^{-i\langle\xi,x\rangle}dx=\widehat{\mathbf 1_T}(\xi)\varphi(-\xi)=\varphi(\xi)\widehat{\mathbf 1_T}(\xi)$, because $\varphi$ is real and even (a product of $J_0(a_k|\omega_k|)$ with $|\omega_k|$ even in $(s,t)$).

(v) Poisson summation. Let $P_s=2\pi/h_s$, $P_t=2\pi/h_t$ and $\Pi(v)=\sum_{m\in\mathbb{Z}^2}G(v+(m_sP_s,m_tP_t))$. By (iii) the sum is locally finite, so $\Pi$ is continuous and periodic, with Fourier coefficients $(P_sP_t)^{-1}\widehat G$ at the dual lattice $h_s\mathbb{Z}\times h_t\mathbb{Z}$. These are absolutely summable: $|\widehat{\mathbf 1_T}|\le\mathrm{area}(T)=\beta^2/2$, and $\sum|\varphi_{100}|<\infty$ over the lattice by Lemma \ref{lem:boxtail}. A continuous periodic function with absolutely summable Fourier coefficients equals its Fourier series at every point, so at $v=0$, $\sum_mG(m_sP_s,m_tP_t)=\frac{h_sh_t}{4\pi^2}\sum\varphi\,\widehat{\mathbf 1_T}$.

(vi) Aliasing. By (iii), a lattice point $m\ne0$ with $G\ne0$ would need $m_sP_s\in(-C,\beta+C)$ and $m_tP_t\in(-\beta-S_d,S_d)$ (both coordinates must be in range). So it is enough that one of the two fails. For $m_s\ge1$, $m_sP_s\ge P_s>C+\beta$; for $m_s\le-1$, $m_sP_s\le-P_s<-C$. For $m_t\ge1$, $m_tP_t>2\beta\ge S_d$; for $m_t\le-1$, $m_tP_t<-2\beta\le-\beta-S_d$. So only $m=0$ contributes, and the left side is $G(0)=\mathbb{P}((F,D)\in T_1)$. The sum on the right is invariant under $(s,t)\mapsto(-s,-t)$ up to complex conjugation, so it is real and equals the sum of real parts. There is no quadrature error. One lattice serves both models.
```{=latex}
\end{proof}
```

```{=latex}
\begin{lemma}[tail zeros: Bessel bound]\label{lem:bessel}
```
Write $\varphi=\varphi_{100}\varphi_{\mathrm{tail}}$ with $\varphi_{\mathrm{tail}}=\prod_{k>100}J_0(a_k|\omega_k|)$. Then $|\varphi_{\mathrm{tail}}-1|\le\min(2,Q)$, with $Q=\tfrac14\sum_{k>100}a_k^2|\omega_k|^2=\tfrac14(s^2M_0-2stM_1+t^2M_2)$, $M_0=\sum_{k>100}a_k^2$, $M_1=\sum_{k>100}a_k^2(1-\cos\theta_k)$, $M_2=2M_1$.

```{=latex}
\end{lemma}
```

<!-- statement
id: AL7
label: PROVED
-->

```{=latex}
\begin{proof}
```
By Bessel's integral and $1-\cos y\le y^2/2$, $0\le1-J_0(x)\le x^2/4$ for all real $x$ [16, (10.9.1)]. Also $|J_0|\le1$. For numbers $z_k\in[-1,1]$, $|\prod z_k-1|\le\sum(1-z_k)$, giving $\le Q$, and $|\prod z_k-1|\le2$. Finally $|\omega_k|^2=s^2-2st(1-\cos\theta_k)+t^2(2-2\cos\theta_k)$.
```{=latex}
\end{proof}
```

```{=latex}
\begin{lemma}[moments beyond the zero list]\label{lem:beyond}
```
Assume RH and LI$_\theta$ with multiplicity. Let $T$ be the height of Lemma \ref{lem:zeros}, $A=2/(\tfrac14+T^2)$, and $T_{2000}=C-\sum_{k\le2000}a_k$. Then every zero beyond the list has $a_k\le A$, $\sum_{k>2000}a_k\le T_{2000}$, and so $\sum_{k>2000}a_k^2g_k\le A\,G\,T_{2000}$ whenever $0\le g_k\le G$.

```{=latex}
\end{lemma}
```

<!-- statement
id: AL8
label: CONDITIONAL
-->

**Hypotheses:** RH and LI$_\theta$ with multiplicity (all zeros simple).

```{=latex}
\begin{proof}
```
By Lemma \ref{lem:zeros} every zero beyond the list has $\gamma>T$, and $w$ is decreasing, so $a_k=2w_k\le A$. Zeros are simple, so $\sum_{k>2000}a_k=T_{2000}$ by Lemma \ref{lem:formula}. Then $\sum a_k^2g_k\le AG\sum a_k$. Without simplicity this fails: a zero of multiplicity $m$ contributes $m\cdot2w$ to $\sum a_k$ and up to $(2mw)^2$ to $\sum a_k^2$.
```{=latex}
\end{proof}
```

```{=latex}
\begin{lemma}[box tail]\label{lem:boxtail}
```
Assume RH. Let $n_s=346$, $n_t=705$, $S_{\max}=n_sh_s\approx22812.0$, $T_{\max}=n_th_t\approx759453.7$ (the lattice terms with $|i|\le n_s$, $|j|\le n_t$ form the box), $\nu(s,t)=\max(|s|/S_{\max},|t|/T_{\max})$ and $p=19.5$. (a) For $\nu(s,t)\ge1$, $|\varphi_{100}(s,t)|\le U_{\max}\,\nu(s,t)^{-p}$ with $U_{\max}=1.9294109\cdot10^{-17}$ and $p=m_{\min}/2$, $m_{\min}=39$. (b) The lattice terms outside the box satisfy $\sum_{\nu>1}|\varphi_{100}||\widehat{\mathbf 1_{T_1^\beta}}|\le2.2349442\cdot10^{-17}$, in units of the raw lattice sum (before the factor $h_sh_t/4\pi^2$).

```{=latex}
\end{lemma}
```

<!-- statement
id: AL9
label: CONDITIONAL
certificate: papers/keiper-li-sign-runs/code/density_results.json
-->

**Hypotheses:** RH (zero list), LI$_\theta$ (for the full model only through $|\varphi_{\mathrm{full}}|\le|\varphi_{100}|$).

```{=latex}
\begin{proof}
```
Envelope. For $x>0$ put $r(x)=\sqrt{2/(\pi x)}\,(1+1/(8x))$. Then $|J_0(x)|\le r(x)$ for all $x>0$ [5, §10.17(iii), $\nu=0$, $l=1$]: $J_0=\mathrm{Re}\,H_0^{(1)}$, and the Hankel expansion of $H_0^{(1)}$ (10.17.5 and 10.17.6) has a remainder after the first term of modulus at most the first neglected term, $|a_1(0)|/x=1/(8x)$, valid since $l=1\ge\max(\nu-\tfrac12,1)$. Also $|J_0|\le1$, and $r$ is decreasing. For $\lambda\ge1$ and $r(x)<1$, $r(\lambda x)\le\lambda^{-1/2}r(x)$, because $\sqrt{2/(\pi\lambda x)}=\lambda^{-1/2}\sqrt{2/(\pi x)}$ and $1+1/(8\lambda x)\le1+1/(8x)$.

Factors. $|\omega_k|=|(s-t(1-\cos\theta_k))+it\sin\theta_k|\ge L_k(s,t):=\max(|t|\sin\theta_k,\ |s|-|t|(1-\cos\theta_k))$. $L_k$ depends on $(|s|,|t|)$ only and $L_k(\lambda q)=\lambda L_k(q)$ for $\lambda\ge0$. So $|\varphi_{100}(q)|\le\prod_{k\le100}\min(1,r(a_kL_k(q)))$ (a factor with $L_k\le0$ is bounded by $1$).

Boundary. Let $\partial R$ be the boundary of $[-S_{\max},S_{\max}]\times[-T_{\max},T_{\max}]$. Each $q$ with $\nu(q)=\lambda\ge1$ is $\lambda p_0$ with $p_0\in\partial R$, and by the symmetry in $|s|,|t|$ it suffices to take $p_0$ on the two edges $\{|s|=S_{\max},0\le t\le T_{\max}\}$ and $\{|t|=T_{\max},0\le|s|\le S_{\max}\}$. Each edge is cut into $4000$ cells. On a cell, with $|t|\in[t_l,t_u]$ and $|s|\ge s_l$ (resp. the fixed value), $L_k(p_0)\ge\max(t_l\sin\theta_k,\ s_l-t_u(1-\cos\theta_k))$. The code evaluates $r(a_k\cdot\text{this lower bound})$ in ball arithmetic and keeps the factors whose upper bound is below $1$: let $m_{\mathrm{cell}}$ be their number and $U_{\mathrm{cell}}$ their product. Since $r$ is decreasing, for $p_0$ in the cell the same factors satisfy $r(a_kL_k(p_0))<1$, so by the envelope step, $|\varphi_{100}(\lambda p_0)|\le\lambda^{-m_{\mathrm{cell}}/2}U_{\mathrm{cell}}$ (the other factors are at most $1$). The certificate stores $U_{\max}=\max U_{\mathrm{cell}}=1.9294109\cdot10^{-17}$ and $m_{\min}=\min m_{\mathrm{cell}}=39$, giving (a) with $p=19.5>2$ (since $\lambda^{-m/2}\le\lambda^{-m_{\min}/2}$ for $\lambda\ge1$). The edge maxima are taken by interval subdivision, not by sampling.

Shell count. Lattice points have $\nu(ih_s,jh_t)=\max(|i|/n_s,|j|/n_t)$, so the number $N(\lambda)$ with $\nu\le\lambda$ satisfies $N(\lambda)\le(2\lambda n_s+1)(2\lambda n_t+1)\le c\lambda^2$ for $\lambda\ge1$, $c=4n_sn_t(1+\frac1{2n_s})(1+\frac1{2n_t})$. By Abel summation, $\sum_{\nu>1}\nu^{-p}=p\int_1^\infty\lambda^{-p-1}(N(\lambda)-N(1))\,d\lambda\le pc\int_1^\infty\lambda^{1-p}d\lambda=pc/(p-2)$.

Conclusion. $|\widehat{\mathbf 1_{T_1^\beta}}|\le\mathrm{area}(T_1^\beta)=\beta^2/2$, so the outside terms sum to at most $(\beta^2/2)\,U_{\max}\,pc/(p-2)$, which the computation evaluates in balls (upper bound $2.2349442\cdot10^{-17}$, stored in the archived density results, Appendix B). The factor $\kappa=h_sh_t/4\pi^2$ is not part of this bound: it enters once, in the final scale $2\kappa/(\theta_1/\pi)$. Finally $\int_{\nu>1}|\varphi_{100}|\le\int_1^\infty U_{\max}\lambda^{-p}\,8S_{\max}T_{\max}\lambda\,d\lambda<\infty$ and $|\varphi_{100}|\le1$ on the box, so $\varphi_{100}\in L^1$.
```{=latex}
\end{proof}
```

**Proof of Theorem D from the lemmas.** Existence and $\delta=2\,\mathbb{P}((F,D)\in T_1)$ are Lemma \ref{lem:density}. By Lemma \ref{lem:lattice}, $\mathbb{P}((F,D)\in T_1)=\kappa\sum_{\Lambda}\varphi\,\mathrm{Re}\,\widehat{\mathbf 1_{T_1^\beta}}$ over the lattice $\Lambda=h_s\mathbb{Z}\times h_t\mathbb{Z}$, $\kappa=h_sh_t/4\pi^2$. Split $\Lambda$ into the box $|i|\le346$, $|j|\le705$ ($693\times1411=977823$ points) and the rest. The summand is invariant under $(s,t)\mapsto(-s,-t)$ ($\varphi$ is even and the real part of the transform is even), so the computation sums the half box $j\ge0$ ($693\times706=489258$ points) with weight $2$ off the row $j=0$ and weight $1$ on it. Inside, write $\varphi=\varphi_{100}+\varphi_{100}(\varphi_{\mathrm{tail}}-1)$ (the Bessel factors of $k>100$ form $\varphi_{\mathrm{tail}}$; the product converges because $\sum a_k^2|\omega_k|^2<\infty$). Then:

- the central sum $\sum_{\mathrm{box}}\varphi_{100}\,\mathrm{Re}\,\widehat{\mathbf 1_{T_1^\beta}}$ is evaluated in balls;
- by Lemma \ref{lem:bessel}, $|\varphi_{\mathrm{tail}}-1|\le\min(2,Q)$, so the second part is at most $E=\sum_{\mathrm{box}}|\varphi_{100}||\mathrm{Re}\,\widehat{\mathbf 1_{T_1^\beta}}|\min(2,Q)$, with each $Q$ bounded above in balls: the part from $k=101,\dots,2000$ by the moments $M_0,M_1,M_2$ from the zero list, and the part from $k>2000$ by $\tfrac14A\,T_{2000}(|s|+|t|\theta_T)^2$ from Lemma \ref{lem:beyond}, with $g_k=|\omega_k|^2\le(|s|+|t|\theta_k)^2\le(|s|+|t|\theta_T)^2$ (as $|e^{i\theta}-1|\le\theta$), $\theta_T=2\arctan\frac1{2T}$;
- outside the box, $|\varphi|\le|\varphi_{100}|$, so those terms sum to at most the tail $\mathcal{T}=2.2349442\cdot10^{-17}$ of Lemma \ref{lem:boxtail}.
Hence $\delta/(\theta_1/\pi)\in\frac{2\kappa}{\theta_1/\pi}\,[\Sigma_0-E-\mathcal{T},\ \Sigma_0+E+\mathcal{T}]$, $\Sigma_0$ the central sum, and the bracket stated in Theorem D is this interval, rounded outward (archived with the certificates, Appendix B). Theorem D$'$ (the $100$-term model under LI$_\theta(100)$) is the same with $E=0$.

# Appendix B: reproduction {-}

Python $3.12$ with python-flint $0.9.0$ (Arb, $128$-bit balls), numpy $2.5.5$, scipy $1.18.1$. The code and certificate files are public at <https://github.com/mik-tf/keiper-li-sign-runs> and will be archived on Zenodo. Scripts and archives are in `code/`; the commands below are run from the repository root, with `P=code` set in the shell, and each writes to a directory given on the command line.

\begingroup\raggedright

- Zeros: `python3 $P/zeros.py 2000 OUT/z2000.json` (about $33$ s). Certificate file: `z2000.json`.
- Theorem A: `python3 $P/certify.py $P/z2000.json 1699 --outdir OUT` (about $2$ minutes per $L$; also $L=1573$). Certificate files: `cert_L1699.json`, `cert_L1573.json`.
- Theorem B: `python3 $P/certify_witness.py $P $P/witness_pos312.txt 300 312 1 OUT/cert_witness_pos312.json` and `python3 $P/certify_witness.py $P $P/witness_neg312.txt 300 312 -1 OUT/cert_witness_neg312.json` (about $90$ s each). Certificate files: `cert_witness_pos312.json`, `cert_witness_neg312.json`.
- Theorem C: `python3 $P/certify_run.py $P/z2000.json $P/torus_results.json OUT` (about $15$ s for the whole table). Certificate files: `cert_run_pos_K700.json`, `cert_run_pos_K1400.json`, `summary.json`.
- Theorems D and D$'$: `python3 $P/certify_density.py $P/z2000.json OUT/density_results.json --workers 16 --floatcheck $P` (about $2$ minutes on $16$ workers; $16$ GB of memory). Certificate file: `density_results.json`.
- Johansson's table counts: `python3 $P/table_sign_changes.py TABLE OUT/table_sign_changes.json`, with `TABLE` the table of [21] (not archived here).
- Window cross-check: `python3 $P/crosscheck_window.py $P --json OUT/crosscheck_window.json` (about $6$ s).
- Search code (optional, not part of any proof): `code/search/` holds the lattice search that found the two witnesses of Theorem B (about $3$ to $4$ CPU hours each; see `code/search/README.md`), and `code/search/torus/` the phase search of Theorem C (see its `README.md`).
- Figure data: `python3 $P/make_figure_data.py` reads only the archived files, and recomputes no certified number.

\endgroup

The runs were made on a $32$-core Linux server. The archived files differ from a re-run only in timing fields (checked for the Theorem A certificate for $L=1573$ and the $K=700$ row of Theorem C). The script `certify.py` does not read the kernel from the archive: it re-solves the linear program for the kernel (HiGHS through scipy) and rounds to integers over $2^{50}$, as in Appendix A. A different solver build could give a slightly different kernel and a slightly different ratio in the last digits, but any kernel it certifies is valid, since only the integers enter the certificate; the archived `cert_L*.json` files carry the numerators.

**Cross-checks.** Two separately written implementations re-checked the window certificates. They share the inequality and the tail argument with the main certificate, so they are checks of the implementation, not independent proofs.

1. An mpmath interval implementation with its own zero list re-checked both window certificates. It reproduces both: the ratios are $0.940423$ for $L=1699$ and $0.998057$ for $L=1573$, against the archived $0.940769$ and $0.998376$. The difference comes from its finer arc grid for the bound on the unlisted zeros, so the archived values are the more conservative. Its zeros and its zero count come from mpmath floating point and are not proof grade.
2. The script `code/crosscheck_window.py` does not import `certify.py`. It re-verifies each of the $2000$ zeros by a sign change of the Hardy function $Z$ at $\gamma\pm10^{-20}$ (its own half-width; the zero list of Lemma \ref{lem:zeros} uses $\pm2^{-20}$), in Arb ball arithmetic at $128$ bits, and uses its own arc grid. It shares with the main certificate the kernel (the numerators read from `cert_L*.json`) and Arb's `zeta_nzeros` count of the zeros up to $T$, which the paper trusts. Its certified ratios, read from `code/crosscheck_window.json` and rounded up at the digits shown, are $0.940453254649$ for $L=1699$ and $0.998084532485$ for $L=1573$, against the archived $0.9407685236$ and $0.9983759146$. Command: `python3 $P/crosscheck_window.py $P --json OUT/crosscheck_window.json` (about $6$ s).

# References {-}

[1] J. B. Keiper, *Power series expansions of Riemann's $\xi$ function*, Math. Comp. 58 (1992), no. 198, 765-773. https://doi.org/10.1090/S0025-5718-1992-1122072-5

[2] H. Xiao, *Recurrence relations of Li coefficients*, arXiv:2006.13103v1 (2020). https://arxiv.org/abs/2006.13103

[3] E. Bombieri and J. C. Lagarias, *Complements to Li's criterion for the Riemann hypothesis*, J. Number Theory 77 (1999), 274-287. https://doi.org/10.1006/jnth.1999.2392

[4] F. Johansson, *Arb: efficient arbitrary-precision midpoint-radius interval arithmetic*, IEEE Trans. Comput. 66 (2017), no. 8, 1281-1292. https://doi.org/10.1109/TC.2017.2690633

[5] NIST Digital Library of Mathematical Functions, section 10.17(iii). https://dlmf.nist.gov/10.17

[6] H. Weyl, *Über die Gleichverteilung von Zahlen mod. Eins*, Math. Ann. 77 (1916), 313-352, Satz 1 (p. 315), Satz 3 and Satz 4 (p. 319).

[7] M. Perreault, *Sign changes of Keiper-Li second differences*, 2026, Zenodo, https://doi.org/10.5281/zenodo.24447746.

[8] X.-J. Li, *The positivity of a sequence of numbers and the Riemann hypothesis*, J. Number Theory 65 (1997), no. 2, 325-333. https://doi.org/10.1006/jnth.1997.2137

[9] H. Davenport, *Multiplicative Number Theory*, Markham, 1967, pp. 83-84

[10] R. S. Lehman, *On the distribution of zeros of the Riemann zeta-function*, Proc. London Math. Soc. (3) 20 (1970), 303-320

[11] R. P. Brent, *On the zeros of the Riemann zeta function in the critical strip*, Math. Comp. 33 (1979), 1361-1372

[12] T. S. Trudgian, *Improvements to Turing's method*, Math. Comp. 80 (2011), 2259-2279. https://doi.org/10.1090/S0025-5718-2011-02470-1 (Theorem 2.1 and Corollary 2.3 are numbered as in the arXiv version, arXiv:0903.1885)

[13] M. Rubinstein and P. Sarnak, *Chebyshev's bias*, Experiment. Math. 3 (1994), no. 3, 173-197. https://doi.org/10.1080/10586458.1994.10504289

[14] A. Feuerverger and G. Martin, *Biases in the Shanks-Rényi prime number race*, Experiment. Math. 9 (2000), no. 4, 535-570. arXiv:math/9910184

[15] A. Haraux, *Uniform oscillation properties of almost periodic functions*, arXiv:2610.06515 (5 Oct 2026), Theorem 2.1.

[16] NIST Digital Library of Mathematical Functions, section 10.9(i), equation (10.9.1). https://dlmf.nist.gov/10.9

[17] M. Grześkowiak, J. Kaczorowski, Ł. Pańkowski and M. Radziejewski, *On the sign changes of $\psi(x)-x$*, Math. Comp. 94 (2025), 3083-3100. arXiv:2408.10399

[18] T. Morrill, D. Platt and T. Trudgian, *Sign changes in the prime number theorem*, arXiv:1910.14203 (2019)

[19] A. Bailleul, *Explicit Kronecker-Weyl theorems and applications to prime number races*, arXiv:2007.05763

[20] A. M. Turing, *Some calculations of the Riemann zeta-function*, Proc. London Math. Soc. (3) 3 (1953), 99-117. https://doi.org/10.1112/plms/s3-3.1.99

[21] F. Johansson, *Rigorous high-precision computation of the Hurwitz zeta function and its derivatives*, Numer. Algorithms 69 (2015), no. 2, 253-270, https://doi.org/10.1007/s11075-014-9893-1; arXiv:1309.2877; table of Keiper-Li coefficients, $n\le10^5$, 20 digits: https://fredrikj.net/math/keiperli100k20d.txt

[22] L. Alpöge, untitled announcement (PDF, 5 pages), 20 November 2026, not peer reviewed, <https://alpo.ge/remark.pdf>. Lean source: a tar archive split into 14 parts, <https://alpo.ge/lean.tar.gz.part01> to `lean.tar.gz.part14`; mirror <https://github.com/Deicyde/riemann-hypothesis>, commit 40e56bab (the unmodified submission, according to the mirror). Accessed 23 November 2026.

[23] Lean FRO and Mathlib Initiative, *Lean verification of the Riemann Hypothesis*, blog post, 21 November 2026, <https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>. Accessed 23 November 2026.

[24] A. M. Odlyzko and H. J. J. te Riele, *Disproof of the Mertens conjecture*, J. reine angew. Math. 357 (1985), 138-160. https://doi.org/10.1515/crll.1985.357.138

[25] A. K. Lenstra, H. W. Lenstra Jr. and L. Lovász, *Factoring polynomials with rational coefficients*, Math. Ann. 261 (1982), no. 4, 515-534. https://doi.org/10.1007/BF01457454
