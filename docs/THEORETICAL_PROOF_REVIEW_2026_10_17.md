# 偶 theta 圆锥丛：2026-10-17 理论证明与依赖核查

这次工作的结论是：在下述通常圆锥丛约定下，整理后的纸面论证推出
\[
X\ \text{在 }\mathbb R\text{ 上有理},\qquad b_0(X(\mathbb R))=1.
\]
证明使用明确列出的经典定理。六段独立审查没有发现致命错误，并补全了此前略写的对象比较、
符号及函数域步骤。**这不等于原命题已通过 Lean 内核检查**；本次没有修改 Lean 源码或增加数学公理。

完整连续论证见 [EVEN_THETA_CONNECTEDNESS_PROOF.md](EVEN_THETA_CONNECTEDNESS_PROOF.md)。
本页给出可核对的依赖链、实质补全及精确形式化边界。

## 1. 题设必须忠实保留

设 \(\pi:X\to S=\mathbb P^2_{\mathbb R}\) 是光滑射影、几何标准的圆锥丛。
“圆锥丛”保留平坦性、相对维数一及光滑几何泛圆锥；不能只留下 Picard 数条件。
其相对反典范模型给出秩三向量丛上的线丛值二次式。判别式是实际行列式有效除子
\(C\)，且 \(C\) 是几何光滑五次平面曲线。

取实际判别覆盖
\[
p:\widetilde C\to C,\qquad
p_*\mathcal O_{\widetilde C}=\mathcal O_C\oplus\eta,\qquad
\mu_0:\eta^{\otimes2}\simeq\mathcal O_C.
\]
这里保留乘法 \(\mu_0\)，不能只保留复化后的覆盖或抽象二阶线丛。
令 \(H=\mathcal O_C(1)\)、\(\theta=\eta\otimes H\)，题设是
\(h^0(C_{\mathbb C},\theta_{\mathbb C})\) 为偶数。

秩三模型的非闭域文献是 Frei–Ji–Sankar–Viray–Vogt 2024，§2，尤其 p.426。
Prokhorov 的对应定理采用代数闭域约定；若引用它，必须补实下降。
[模型审查](review/ORIGINAL_CONIC_MODEL_2026_10_17.md) 用真实反典范推前层、评价映射和理想层
写出了下降，不附加实点或向量丛分裂假设。

## 2. 没有循环的推导顺序

下表“自推”表示正文或链接审查给出计算；“引用”表示使用所列文献的精确命题。

| 输入 | 输出 | 依据及位置 |
| --- | --- | --- |
| 光滑五次曲线、\(\theta^2=H^2\)、偶性 | \(h^0(\theta)=0\) | 自推：两个独立截面给出 \(AD=B^2\)，UFD 及除子消去迫使 \(\theta=H\)、\(h^0=3\)；截面限制用 Stacks 01XT |
| 上述非有效实 theta | 实对称 \(5\times5\) 线性矩阵网 \(M(t)\)，\(\det M=0\) 定义 \(C\) | Beauville，Proposition 4.2(a)，并核对 §0.3、Theorem B、Corollary 2.4 |
| 实际原覆盖及该矩阵网 | 二者实际实判别覆盖同构 | 自推：Tor、迹零线、伪直线的惯性及正实常数扭曲 |
| 实覆盖同构 | \([C_0(q)]=\alpha=[X_{\eta_S}]\) | 自推余数和实点评估；Poonen 6.8.3、6.9.9、6.6.7(i) |
| 上述 Brauer 等式、光滑判别式 | \(q\) 在每个排序下不定 | 自推定号区域边界矛盾；Marker 7.14、7.15 将严格不等式从实闭扩域传回实数 |
| \(\operatorname{ind}C_0(q)\le2\)、所有排序不定、\(F=\mathbb R(x,y)\) | \(q\) 在 \(F\) 上各向同性 | KMRT 16.3、16.5；EKM 8.4、31.22、35.29；中间 Clifford/Pfister 计算自推 |
| 泛型二次超曲面有 \(F\)-点 | 三个 \(Q_i\) 有公共实点 \(P\) | CT–Levine Theorem 3 给约化指数一；自推实闭点次数只能为一或二 |
| 公共点、实际几何 Jacobian 条件 | 有理整开集 \(U\subset Z\)，实际 \(U\to S\) 支配 | 自推极化独立、非零子式、消元、纤维维数；该矩阵输入端点已有 Lean 证明 |
| 支配开集、\([C_0(q)]=\alpha\) | \(\mathbb R(X)\simeq\mathbb R(u,v,w)\) | 自推泛纤维局部化、双曲约化、四元数范数；Poonen §4.5.1 分类图；Stacks 0BXN、0BXP |
| 光滑射影实有理三维簇 | \(X(\mathbb R)\ne\varnothing\) 且连通 | 自推余维二基点集避障；Poonen 3.5.75、Remark 3.5.76 给每个实邻域的稠密性 |

\(\eta_S\) 在此表示参数平面的泛点，与覆盖的迹零线 \(\eta\) 区分。
Brauer 等式在公共点存在性之前证明；公共点没有被用于反推这个等式。

## 3. 实覆盖比较中补上的细节

对 Beauville 分辨率扭曲再限制到 \(C\)，完整序列为
\[
0\to\operatorname{Tor}_1(i_*\theta(2),\mathcal O_C)
\to\mathcal O_C^5\xrightarrow{M}H^{\oplus5}\to\theta(2)\to0.
\]
不能假定限制保持左端单射。用五次超曲面序列直接算出
\[
K=\operatorname{Tor}_1(i_*\theta(2),\mathcal O_C)
=\theta(-3)=\theta^{-1}(-1).
\]
故秩四商 \(W=\mathcal O_C^5/K\) 的判别线是
\[
D_4=\det W\otimes H^{-2}=\theta(-1)=\eta.
\]

这仍只识别了线丛。实际两种平方配对相差常数
\(\lambda\in\Gamma(C,\mathcal O_C)^*=\mathbb R^*\)。
奇次数曲线有伪直线分支 \(J\)。原秩三模型值线丛的次数 \(m\) 满足
\(3m-2e=5\)，所以在 \(J\) 上不定向；矩阵网的值线丛 \(H\) 也不定向。
沿一圈取局部标架，终点矩阵为起点矩阵的负合同，连续非退化性于是迫使惯性平衡：
原秩二商是 \((1,1)\)，秩四商是 \((2,2)\)。

因此两个覆盖在任取一个 \(J\) 上实点处都分裂，推出 \(\lambda>0\)；
把线丛同构乘以 \(\lambda^{-1/2}\) 就得到保持乘法的实覆盖同构。
这里只用了逐点分裂，没有声称覆盖在整条圆周上平凡。

完整推导：[THETA_AND_REAL_COVERS_2026_10_17.md](review/THETA_AND_REAL_COVERS_2026_10_17.md)。

## 4. Brauer 等式和各向同性为何适用

五维对角型的直接 Clifford 计算给
\[
[C_0(\langle a,b,c,d,e\rangle)]
=(-ab,-ac)+(abcd,abce).
\]
沿简单退化 \(e=\varpi u\) 的余数为 \(abcd\)；原三维型
\(\langle A,B,\varpi U\rangle\) 的余数为 \(-AB\)。
它们正是前节比较的实际覆盖。其余素除子处局部型非退化；奇数维缩放不改变该 Brauer 类，
所以无穷远也没有额外余数。

纯性和 \(\operatorname{Br}(\mathbb P^2_{\mathbb R})=\operatorname{Br}(\mathbb R)\)
使两类之差为常数。在伪直线附近的非判别实点，原圆锥和五维 Clifford 类均分裂，
故该常数为零。评估发生在共同不分歧开集，未在判别曲线上非法评估分歧类。

若矩阵网有定号成员，定号开集的边界给出秩四半定号退化，其正判别值使原覆盖分裂。
原秩二不定号块在邻域保持不定，故原圆锥类在邻域非判别实点为零；
但靠近边界的定号五维成员 Clifford 类为 Hamilton 类，矛盾。
对任意排序取 \(F\) 的实闭包，定号性由有限个 Sylvester 严格不等式表达；
实闭域模型完全性将任何这样的解传回实数，再次矛盾。

随后固定实际 \(d=\det q\)，令 \(r=q\perp\langle-d\rangle\)。有
\[
\operatorname{disc}(r)=1,\qquad C_0(r)\simeq C_0(q)\times C_0(q).
\]
Albert 定理用指数至多二推出 \(r\) 各向同性。分裂双曲平面并作 Witt 消去得到
\[
q\simeq a\pi\perp\langle d\rangle
\subset \Phi=a\pi\otimes\langle1,d/a\rangle,
\]
其中 \(\pi\) 是二重 Pfister 型，\(\Phi\) 维数八。
每个排序下 \(q\) 不定，故包含它的 Pfister 相似型 \(\Phi\) 不能定号，只能双曲。
EKM 31.22 给 \([\Phi]\) 为 Witt 挠元，EKM 35.29 给 \(I^3(F)\) 无挠，
所以 \(\Phi\) 在 \(F\) 上双曲。其四维全各向同性子空间与 \(q\) 的五维空间必有非零交，
因为 \(4+5>8\)，即得 \(q\) 各向同性。

这里没有使用 \(I^3(F)=0\)。也没有省略“所有排序”：
仅检查普通实参数，必须先通过实闭域转移才能调用签名定理。
审查还给出三变量域上的反例，说明二维函数域条件不可删去。

完整推导：
[BRAUER_AND_ORDERINGS_2026_10_17.md](review/BRAUER_AND_ORDERINGS_2026_10_17.md)；
[ALBERT_PFISTER_2026_10_17.md](review/ALBERT_PFISTER_2026_10_17.md)。

## 5. 从泛型点到公共实点

令 \(\Gamma=V(Q_0,Q_1,Q_2)\subset\mathbb P^4_{\mathbb R}\)。
CT–Levine Theorem 3 的参数是 \(r=2,d=2,n+1=5\)，数量条件为 \(5\ge4\)；
不需要另证 \(\Gamma\) 光滑或为完全交。

该文的约化指数是完整指数的平方自由部分，保留因子 \(2\)。
泛型二次超曲面有有理点，给 \(I_{\rm red}(\Gamma)=1\)，所以 \(I(\Gamma)=1\)。
实数上的闭点剩余域只有 \(\mathbb R,\mathbb C\)，次数为一或二；
若没有实点，所有零循环次数均为偶数，矛盾。

完整核查：
[ZERO_CYCLE_COMMON_POINT_2026_10_17.md](review/ZERO_CYCLE_COMMON_POINT_2026_10_17.md)。

## 6. 实际泛纤维比较：本次的主线简化

在公共点取坐标 \(P=e_0\)，写
\[
Q_t(x_0,y)=2x_0l_t(y)+r_t(y),\qquad
Z=\{l_t(y)=r_t(y)=0\}\subset S\times\mathbb P^3.
\]
非零二阶子式给出实际有理开集 \(U\)，且实际投影 \(U\to S\) 支配。
这是后半段的出发点，不允许将任意有理簇或任意参数映射换进来。

在 \(F=\mathbb R(S)\) 上，
\[
W=P^\perp/FP\simeq(\ker l_t,r_t|_{\ker l_t})
\]
为非退化三元二次空间。其圆锥 \(C_r\) 就是 \(Z_{\eta_S}\)。
支配性保证 \(U_{\eta_S}\) 非空，所以它是 \(C_r\) 的非空开集。
取实际坐标环嵌入 \(A\hookrightarrow B\) 及 \(T=A\setminus\{0\}\)，有
\[
\operatorname{Frac}(T^{-1}B)=\operatorname{Frac}(B),\qquad
F(C_r)=\mathbb R(U).
\]
这是保持实际参数域 \(F\) 的识别，不依赖整个 \(Z\) 的不可约性。
泛纤维的基变换是局部化，所以 reduction 的兼容性由
\(T^{-1}\sqrt I=\sqrt{T^{-1}I}\) 直接证明，而非假定任意基变换保持约化。

双曲约化的实际 Clifford 等式是
\[
C_0(q)\simeq M_2(C_0(r)).
\]
前面已经建立 \([C_0(q)]=[X_{\eta_S}]\)，因此两个三元圆锥的四元数类相同，
从而在 \(F\) 上同构。最终
\[
\mathbb R(X)=F(X_{\eta_S})
\simeq_F F(C_r)=\mathbb R(U)
\simeq_{\mathbb R}\mathbb R(u,v,w).
\]
这一步同时说明了为什么“有理关联开集”足够，以及为什么实际支配性不可省略。

最后，对 \(\mathbb P^3\dashrightarrow X\) 的齐次坐标约去公因子，基点集余维至少二。
任意两个剩余实点可经第三个实点用两条射影直线连接，第三点选在相应两个真闭 join 之外。
于是映像连通。该映像包含双有理同构开集的实点；光滑实点的局部稠密性使它在整个
\(X(\mathbb R)\) 中稠密，而连通集的闭包连通。因此 \(b_0=1\)。

完整推导：
[INCIDENCE_TO_CONNECTEDNESS_2026_10_17.md](review/INCIDENCE_TO_CONNECTEDNESS_2026_10_17.md)。

## 7. 形式化边界

这次已把上述纸面连接写出来，不能再把它们笼统称为“只差调用一篇论文”。
它们需要自己的 Lean 对象识别、代数计算和拓扑证明。

已通过 Lean 的相关端点仍是：从矩阵网、公共非零各向同性点及实际几何 Jacobian 证书，
得到实际非空整有理开集及其支配参数投影。当前尚未在 Lean 中完成：

- 从原圆锥丛及实际覆盖获得所有这些输入，包括实对称表示和公共实点；
- 本页的实覆盖、Brauer、Albert–Pfister、CT–Levine 链；
- 实际泛纤维与局部化函数域的上述比较，以及与原圆锥的同构；
- 从原假设推出最终实点集连通的定理。

整个关联概形不可约及 \(U\) 在其中稠密，已不是本条证明路线所需的额外目标。
本轮仅更新数学文档，沿用原有代码验证记录，没有把纸面审查记作新 Lean 证明。
