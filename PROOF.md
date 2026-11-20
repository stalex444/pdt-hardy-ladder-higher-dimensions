# The sharp four-level two-step Hardy bound

Fix a pure bipartite state with four positive Schmidt coefficients proportional to \(d_1,d_2,d_3,d_4\). Each party has three binary settings. Impose the five ideal Boschi–Hardy zero probabilities. Define

$$
s_{ij}=\frac{d_i d_j^5-d_j d_i^5}{d_i^5+d_j^5},\qquad E_{ij}=s_{ij}^2,\qquad
K=\max\{E_{12}+E_{34},E_{13}+E_{24},E_{14}+E_{23}\}.
$$

**The maximum success probability over all complex binary measurements is \(K/\sum_i d_i^2\).** A measurement that acts independently on each of the two pairs in a maximizing partition attains it. This is an existence statement about an optimal measurement and allows other optimizers.

The absolute maximum is \(p_*=(8\rho^2+\rho-11)/25\), where \(\rho>1\) and \(\rho^3=\rho+1\). A rank-four pure state reaches it **if and only if its four coefficients can be partitioned into two pairs each having smaller-to-larger ratio \(\rho^{-2}\)**. Equivalently the multiset is proportional to \(\{a,a\rho^{-2},b,b\rho^{-2}\}\) for positive \(a,b\). Both pair weights are free. The same ceiling holds for mixed states of Schmidt number at most four under the ideal zeros.

## 1. The measurement score as a quadratic quotient

Work with unnormalized success and put \(D=\operatorname{diag}(d_i)\). The five zeros reduce the fixed-state upper bound, with equality attainable, to the maximum over terminal subspaces \(U\) of

$$
F(D,U)=\|P_{(D^5 U)^\perp}\,D P_U\|_{\mathrm{HS}}^2.
$$

The rank-one and rank-three cases both have maximum \(\max_{i<j}E_{ij}\le K\). The zero and full subspaces give zero. For general binary effects, replacing outcome one by its support projector preserves the forbidden zeros and can only increase terminal success. These results reduce the new argument to a complex two-plane. [Five-zero subspace reduction](#the-five-zero-conditions) · [Rank-one proof](HardyRankOne.lean) · [Effect rounding](HardyEffects.lean)

Let \(H=D^{5/2}U\), called the midpoint plane here. Index its six squared two-row minors by two-element subsets \(I\subset\{1,2,3,4\}\) and write them \(m_I\). A common positive scale is immaterial. For \(I=\{i,j\}\), put \(t_I=(d_i d_j)^5\) and \(q_I=m_I/t_I\). These are the squared minors of \(U\) up to scale. The four-level trace formula gives \(F=N(m)/B(m)\), where

$$
\begin{aligned}
T_k&=\sum_{i<j}q_{ij}(d_i^k+d_j^k),&
J_k&=\sum_{i<j}q_{ij}(d_i d_j)^k,\\
C&=\sum_{i<j}q_{ij}(d_i^{10}d_j^6+d_j^{10}d_i^6),&
N&=T_2J_{10}-T_6 C+J_6T_{10},\\
B&=\left(\sum_I m_I/t_I\right)\left(\sum_I m_I t_I\right)>0.
\end{aligned}
$$

Both \(N\) and \(B\) are homogeneous quadratics. Write \(G_K=KB-N\). We prove \(G_K(m)\ge0\) for every feasible \(m\). [Gram-matrix calculation](HardyBornBridge.lean)

## 2. Which coefficients of the gap matter

The coefficient of \(m_I^2\) in \(G_K\) is \(K\). If \(I,J\) share an index and their differing labels are \(u,v\), the coefficient of \(m_I m_J\) is

$$
c(u,v)=(K-E_{uv})(r+r^{-1})-2E_{uv},\qquad r=(d_u/d_v)^5.
$$

For a direct derivation, restrict the quadratic to these two minor coordinates. The common coordinate spans one line by itself; the other line lies on labels \(u,v\). Its midpoint has squared weights \(x=m_I,y=m_J\). The denominator is \(x^2+y^2+(r+r^{-1})xy\) and the numerator is \(E_{uv}(2+r+r^{-1})xy\). These polynomial restrictions determine the coefficients. The three coefficients of \(m_I m_{I^c}\) can be left arbitrary throughout the balancing step.

Group the six entries into the three complementary pairs \(12|34,\ 13|24,\ 14|23\). Between any two such groups there are two adjacent coefficients, \(c\) and \(c'\). Their differing label pairs are disjoint and form a perfect matching. In particular \(K\ge E+E'\). Since \(r+r^{-1}\ge2\) and \(K\ge E\), we have \(c\ge2K-4E\), whence **\(c+c'\ge0\)**.

## 3. From an arbitrary plane to a balanced gap

In complementary pair \(i\in\{1,2,3\}\) call its larger entry \(h_i\) and smaller entry \(l_i\), and set \(g_i=\sqrt{h_i l_i}\), \(a_i=h_i-l_i\). Write \(m^0\) for the six-vector with both entries of pair \(i\) equal to \(g_i\). Ties can be ordered either way.

For two groups \(i,j\), let \(c_{ij}\) be the coefficient linking the selected higher edges, and \(b_{ij}\) the coefficient linking a higher edge to the lower edge in the other group. Complementing both edges leaves their coefficient unchanged. Direct expansion gives the exact identity

$$
G_K(m)-G_K(m^0)=
 K\sum_i a_i^2+\sum_{i<j}c_{ij}a_i a_j+
 \sum_{i<j}(c_{ij}+b_{ij})
       \big(\sqrt{h_i l_j}-\sqrt{l_i h_j}\big)^2 .
$$

The products within each complementary pair agree before and after balancing. The diagonal difference is \(K(h_i-l_i)^2\). The two adjacent differences yield the displayed square and \(c_{ij}a_i a_j\). These statements also hold when a minor vanishes.

The first two terms together are nonnegative. Choosing one edge from each complementary pair gives either a star with three leaves or a triangle. In a star, assign to each selected edge its leaf label. In a triangle, assign it the triangle vertex missing from that edge. In either case two selected edges have exactly their two assigned labels as their differing coordinates, possibly in reverse order. Denote the three corresponding Schmidt coefficients by \(x_i\). The resulting quadratic is

$$
K\left(\sum_i a_i/x_i^5\right)\left(\sum_i a_i x_i^5\right)
-\left(\sum_i a_i/x_i^3\right)\left(\sum_i a_i x_i^5\right)
+\left(\sum_i a_i x_i\right)^2 .
$$

This is the rank-one Hardy gap with nonnegative midpoint weights \(a_i\). To see the sign directly, the scalar pair inequalities \(E_{ij}\le K\) imply that there exists \(t\) with \(|x_i-tx_i^5|\le\sqrt K\) for all three labels. Indeed the three allowed intervals for \(t\) intersect pairwise and hence have a common point. Write \(M=\sum a_i x_i^5\). The quadratic equals

$$
 M\sum_i\frac{a_i}{x_i^5}\bigl[K-(x_i-tx_i^5)^2\bigr]
 +\bigl(\sum_i a_i x_i-tM\bigr)^2\ge0.
$$

Section 2 proves the sign of every squared remainder. Consequently **\(G_K(m)\ge G_K(m^0)\)**. The comparison is between the denominator-cleared gaps; the actual Hardy score may increase or decrease on balancing.

## 4. The balanced gap for complex planes

Index the three perfect matchings by \(A,B,C\). The three lengths \(g_A,g_B,g_C\) satisfy the triangle inequalities by the Plücker relation on the original *complex* minors. For example the length associated to \(12|34\) is \(|z_{12}z_{34}|=\sqrt{m_{12}m_{34}}\). For each matching \(A\) let \(v_A\) have entry zero on its two edges and one on all other edges. Then \(m^0=\sum_A u_Av_A\) with \(u_A=(g_B+g_C-g_A)/2\ge0\). This includes a degenerate triangle and the zero vector.

Put \(\Pi=\prod_i d_i^5\) and \(L_A=\sum_I(v_A)_I/t_I\). On balanced vectors \(B=\Pi(\sum_A u_A L_A)^2\) because \(t_I t_{I^c}=\Pi\). If \(A=(ij)(kl)\), then \(L_A=(d_i^{-5}+d_j^{-5})(d_k^{-5}+d_l^{-5})\). Let \(K_A=E_{ij}+E_{kl}\).

To determine the signs of every coefficient of the homogeneous quadratic \(G_K(\sum_Au_Av_A)\), it suffices to compute its restrictions to two vertices at a time. For matchings \(A,B\) split the four coordinates into two groups of two so that both matchings join the groups. A midpoint plane with minors proportional to \(xv_A+yv_B\), \(x,y\ge0\), is the column space of \(\binom{I}{O}/\sqrt2\), with a two-by-two real orthogonal matrix \(O\) chosen so the squared direct-entry weight is \(x/(x+y)\). Its orthogonal complement has the minus sign on the lower block. Passing from midpoint to terminal spaces multiplies both frames by \(D^{-5/2}\). Their two Gram matrices are the same, \(S/2\), and the cross matrix with \(D\) between them is \(H/2\), where

$$
S=D_1^{-5}+O^* D_2^{-5}O,\qquad H=D_1^{-4}-O^*D_2^{-4}O .
$$

The success is therefore \(\operatorname{tr}((S^{-1}H)^2)\). In dimension two the determinant of a diagonal matrix plus a unitarily conjugated diagonal matrix is the mixture of the direct and crossed permutation determinants, with weights \(|O_{11}|^2,1-|O_{11}|^2\). Apply this identity to \(\det(zS-H)\) and normalize by its leading coefficient. The monic mixture weight of \(A\) is \(\lambda=xL_A/(xL_A+yL_B)\). Write \(T_A\) and \(T_B\) for the sums of the two signed roots for each matching, with each edge oriented from the first group to the second; the root on \(ij\) is \(s_{ij}\). The sum of squared roots of a monic quadratic is its squared root sum minus twice its root product. Thus the exact mixed score is

$$
\lambda K_A+(1-\lambda)K_B-\lambda(1-\lambda)(T_A-T_B)^2 .
$$

In particular, even when two leading pairings tie, mixing them in this family can only maintain or reduce the score. At an interior mix equality with the better endpoint requires both equal scores and equal signed root sums.

Multiplication by the balanced denominator gives, on this two-vertex face,

$$
\frac{G_K(xv_A+yv_B)}{\Pi}
=(xL_A+yL_B)\big[xL_A(K-K_A)+yL_B(K-K_B)\big]
+xyL_A L_B(T_A-T_B)^2 .
$$

Every coefficient on the right is nonnegative, including the mixed coefficient. All three square coefficients and all three cross coefficients of the full three-variable quadratic occur on these faces. Thus \(G_K(m^0)\ge0\) for every nonnegative triple \(u\), including the interiors arising from complex planes. Together with Section 3 this proves the upper bound for every four-level plane.

## 5. Attainment, mixtures, and scope

On each edge \(ij\) of a maximizing matching choose the terminal line with squared coordinates proportional to \(d_j^5,d_i^5\). It attains \(E_{ij}\). Taking the orthogonal sum of the two line strategies preserves all five zeros and adds their scores. This gives equality with \(K\). The sharp two-qubit theorem bounds every \(E_{ij}\) by \(p_*(d_i^2+d_j^2)\), with equality precisely at smaller-to-larger ratio \(\rho^{-2}\). Both terms in an attaining matching must saturate to reach \(p_*\), proving the spectral equality criterion. [Scalar comparison](HardyPairBound.lean) · [Registered two-qubit theorem](https://github.com/stalex444/hardy-ladder/tree/5764ec4a239fcb14f8de263372fc906bd217f349)

For a finite mixture with Schmidt number at most four, all positive-weight components inherit each exact zero by nonnegativity. Compressing to the positive Schmidt support of each component preserves the relevant probabilities and produces binary effects. Apply the fixed-spectrum theorem to rank four and the earlier bounds to ranks one through three, then average. A given mixture attaining \(p_*\) must attain it on every positive-weight component. [Mixture argument](HardyFourEnsemble.lean)


## The five zero conditions

Let \(A_i,B_i\) be outcome-one subspaces, with Bob's space entrywise conjugated in the Schmidt basis. Then \(p(A,B)=\|P_A D P_B\|_{\rm HS}^2\). Set \(A_0=S\). The five zero events require
\[
 B_0\perp DS,\quad D A_1\subset B_0,\quad D B_1\subset S,\quad
 D A_2\subset B_1,\quad D B_2\subset A_1.
\]
The endpoints are contained in \(U=D^{-2}S\) and \(V=D^{-2}(DS)^\perp=(D^5U)^\perp\), respectively. They attain these maximal spaces simultaneously by taking \(B_0=(DS)^\perp\), \(A_1=D^{-1}B_0\), \(B_1=D^{-1}S\), then \(A_2=D^{-1}B_1\) and \(B_2=D^{-1}A_1\). Enlarging either endpoint subspace increases the joint probability weakly, by positivity of the Born rule. Conversely any \(U\) occurs, with \(S=D^2U\). Consequently the exact fixed-state optimum is
\[
 \max_{U\subseteq\mathbb C^n} F(D,U),\qquad
 F(D,U)=\|(I-P_{D^5 U})D P_U\|_{\rm HS}^2.
\]
The involution \(U\mapsto V=(D^5U)^\perp\) switches the endpoints, preserves \(F\) and exchanges ranks \(r,n-r\). In fact \(D^5 V=U^\perp\). Ranks zero and \(n\) yield zero.


## Twelve distinct Schmidt weights

Write $t=1/\rho$. The optimal qubit has squared Schmidt coefficients $t,t^5$, whose sum is one. Choose six sector weights $w_i=(1,2,3,5,7,11)_i/29$. The pure state has squared Schmidt coefficients $w_i t,w_i t^5$ in sector $i$. Block-diagonal local measurements apply the same optimal two-qubit settings to each sector. For a matched pair of sectors the joint amplitude acquires the factor $\sqrt{w_i}$. For mismatched sectors it vanishes. Summing the squared amplitudes therefore preserves every joint probability. Lean also proves injectivity of the twelve squared weights, including across the two columns. [Sector construction and exact witness](HardyDirectSum.lean)
