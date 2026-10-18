# 实际二次空间的双曲分解与偶 Clifford 代数比较

本节接续[实际扩域与整性](CONIC_FIELD_BASE_CHANGE.md)，把已经构造的实际三元圆锥方程接回原五维泛二次空间。新增比较使用明确的可逆坐标矩阵，并诱导实际偶 Clifford 子代数之间的同构。构建和公理审计状态统一见[核验说明](../verification/README.md)。

这一步证明的是二次空间同构及其诱导的偶 Clifford 同构。尚未证明

\[
C_0(H\perp r)\simeq M_2(C_0(r)),
\]

也尚未与原题圆锥丛的 Brauer 类或原实点集连通性接通。

## 1. 保留原限制矩阵的显式基变换

令 \(K\) 为域，\(2\ne0\)，\(A\) 为一个对称 \((n+2)\) 阶矩阵，满足

\[
A_{00}=0,\qquad A_{\rho+1,0}\ne0.
\]

使用此前的 `incidencePivotEquiv ρ`，固定第零坐标，把选定的极化主元移到第一坐标，其余坐标仍按 `ρ.succAbove` 排列。记排列后的矩阵为

\[
A'=\operatorname{incidencePivotMatrix}(A,\rho),\qquad
a=A'_{10},\quad c=A'_{11},\quad
b_i=A'_{i+2,0},\quad d_i=A'_{1,i+2}.
\]

此前的极化消元列向量正是

\[
L_i=e_{i+2}-\frac{b_i}{a}e_1,
\qquad
R=L^{\mathsf T}A'L
  =\operatorname{incidenceRestrictedMatrix}(A').
\]

这里的 \(R\) 是原项目已有的实际限制矩阵。新构造没有用一个任意同构的三元型替换它。定义

\[
e=e_0,\qquad
f=\frac1a e_1-\frac{c}{2a^2}e_0,
\qquad
w_i=L_i-
  \left(\frac{d_i}{a}-\frac{cb_i}{a^2}\right)e_0,
\]

并取列矩阵 \(B'=[e,f,w_0,\ldots,w_{n-1}]\)。
`IncidenceHyperbolicDecomposition.lean` 证明

\[
\det B'=a^{-1}\ne0,\qquad
(B')^{\mathsf T}A'B'=
\begin{pmatrix}
0&1&0\\
1&0&0\\
0&0&R
\end{pmatrix}.
\]

该块矩阵记为 `incidenceHyperbolicSumMatrix R`。其二次表达式精确为

\[
2x_0x_1+\sum_{i,j}R_{ij}x_{i+2}x_{j+2}.
\]

因此这里的双曲平面采用 \(2x_0x_1\) 规范；没有把矩阵的非对角系数与二次多项式系数混同。证明先检查明确的矩阵乘积，再以三角矩阵行列式公式证明可逆性。

`incidencePivotHyperbolicBasisMatrix A ρ` 把这些列移回原坐标，得到实际矩阵 \(B\)。对应端点是

```lean
incidencePivotHyperbolicBasisMatrix_det_ne_zero A ρ hpivot

incidencePivotHyperbolicBasisMatrix_congruence
  h2 A hA hbase ρ hpivot
```

第二个端点的结论字面为

```lean
B.transpose * A * B =
  incidenceHyperbolicSumMatrix
    (incidenceRestrictedMatrix (incidencePivotMatrix A ρ))
```

上述构造只要求列出的特征条件、对称性、各向同性坐标和非零主元，不要求另给同构、双曲分解或 \(\det A\ne0\)。在实际泛矩阵的应用中，所需主元由此前的几何 Jacobian 及支配性论证产生。

## 2. 从矩阵到实际二次空间

`MatrixQuadraticClifford.lean` 定义

```lean
matrixQuadraticForm A : QuadraticForm K (Fin (n + 2) → K)
```

并证明它的值等于既有 `matrixQuadraticPolynomial A` 的求值，即 \(x^{\mathsf T}Ax\)。它由矩阵所确定的实际双线性型构造，不是另行引入的抽象二次型。

任何已经证明的可逆矩阵合同 \(B^{\mathsf T}AB=N\) 都给出实际

```lean
(matrixQuadraticForm N).IsometryEquiv (matrixQuadraticForm A)
```

其中正向线性映射为 \(x\mapsto Bx\)，逆向为 \(x\mapsto B^{-1}x\)。
`IncidenceHyperbolicClifford.lean` 的 `incidencePivotQuadraticIsometry` 用第一节构造的矩阵和已经证明的合同，得到

\[
H\perp q_R\simeq q_A.
\]

同构及其作用公式均有定义和证明，调用者不需要提供一个二次空间同构作为额外输入。

## 3. 实际偶 Clifford 子代数及生成元相容性

本轮使用 mathlib 的实际对象 `CliffordAlgebra.even Q`。一般二次空间等距映射通过偶 Clifford 代数的泛性质给出 `evenCliffordMap`；等距同构及其逆映射进一步给出 `evenCliffordEquivOfIsometry`。

该映射还被证明等于全 Clifford 代数上 `CliffordAlgebra.map` 的限制。它在偶生成元上的公式为

\[
\iota_N(x)\iota_N(y)
\longmapsto
\iota_A(Bx)\iota_A(By).
\]

这里使用的是两个嵌入向量的乘积，它属于偶子代数；没有把一般单个向量的 Clifford 嵌入当成偶元素。同构是原系数域上的 `AlgEquiv`，因此保留实际系数作用。

`incidencePivotEvenCliffordEquiv` 的方向是

\[
C_0(H\perp q_R)\xrightarrow{\sim}C_0(q_A),
\]

取其逆即得相反方向。`incidencePivotEvenCliffordEquiv_ι` 保留上面的具体生成元公式。这个结论来自已经构造的实际等距同构，没有把待证的 Brauer 类相等作为输入。

## 4. 与原关联模型、参数域和公共点端点的连接

在实际矩阵网应用中，系数域仍是此前的
`incidenceParameterSubfield M k p h`，即实际 Cramer 参数子域。五维矩阵是同一个 `incidenceGenericMatrix M k p h`，三维矩阵是同一个

```lean
incidenceGenericConicMatrix M k p h ρ
```

后者定义了已经证明整、光滑并在任意宇宙零扩域后仍整的实际射影圆锥。归一化接口为

- `incidenceGenericQuadraticIsometry`：原实际泛二次空间与该精确三元型的双曲和等距；
- `incidenceGenericEvenCliffordEquiv`：同一实际参数域上的偶 Clifford 代数同构。

`IncidenceGenericClifford.lean` 进一步给出统一端点

```lean
exists_fieldExtension_integral_smooth_genericConic_clifford_of_common_point
```

其输入是无限域、\(2\ne0\)、实际对称五阶矩阵网、非零公共各向同性向量和实际行列式的几何 Jacobian 证书。它内部选择一次公共点归一化、参数图、空间图、非零子式和极化主元，在同一组选择下同时保留：

- 实际三元矩阵的对称性和非退化性；
- 整条实际圆锥的整性及原结构态射的相对维数一光滑性；
- 对每个 `L : Type` 扩域，原圆锥实际范畴拉回的整性；
- 保持原实际参数域和基域作用的函数域比较；
- 原实际关联泛纤维到该圆锥的非空像开同构；
- 该同一个三元型的双曲等距同构，以及原实际参数域上的偶 Clifford 同构；这些比较同时到达归一化泛矩阵和按同一组参数求值的原矩阵网。

不存在重新选择一个无关圆锥或无关参数域的步骤。统一端点将同构作为构造出的存在性结论；具体作用公式由前面的定义和生成元定理提供。

## 5. 返回原矩阵网，同时保留原参数嵌入

`IncidenceCliffordNormalization.lean` 补上公共点归一化前后的实际二次空间比较。为区别第一节的双曲基变换，此处把公共点归一化矩阵记为 \(G\)。设

\[
M_i^{G}=G^{\mathsf T}M_iG,\qquad
S=\operatorname{incidenceParameterSubfield}(M^{G},k,p,h),
\qquad
t_i=\operatorname{incidenceGenericParameter}(M^{G},k,p,h)_i.
\]

这里 \(S\) 和 \(t_i\) 始终来自同一个已经选定的归一化关联图。`incidenceOriginalGenericMatrix M G k p h` 在这个 \(S\) 中定义为

\[
A_{\mathrm{orig}}=\sum_i t_i\,(M_i)_S.
\]

`incidenceOriginalGenericMatrix_eq_evaluation` 证明这正是原矩阵网扩系数后的字面求值。没有改用一个由原矩阵网重新生成的 Cramer 子域，也没有改变此前函数域比较中的参数域嵌入。

令 \(G_S\) 为 `G.map (algebraMap K S)`，\(A_{\mathrm{norm}}\) 为归一化矩阵网的既有实际泛矩阵。新增的实际合同定理为

\[
G_S^{\mathsf T}A_{\mathrm{orig}}G_S=A_{\mathrm{norm}}.
\]

这由实际矩阵网的定义、系数映射与求和及矩阵乘法的相容性推出。由
\(\det G_S=\operatorname{algebraMap}_{K,S}(\det G)\) 和域嵌入的单射性，证明 \(\det G_S\ne0\)，不另加扩域后的可逆性假设。

相应接口是

- `incidenceNormalizationQuadraticIsometry`，其正向映射为 \(x\mapsto G_Sx\)；
- `incidenceNormalizationEvenCliffordEquiv`，为同一个 \(S\) 上的实际偶 Clifford 同构，由一般生成元定理 `evenCliffordEquivOfIsometry_ι` 和实际等距的 `_apply` 公式，它将 \(\iota_{\mathrm{norm}}(x)\iota_{\mathrm{norm}}(y)\) 送至 \(\iota_{\mathrm{orig}}(G_Sx)\iota_{\mathrm{orig}}(G_Sy)\)。

再与前面的实际双曲基变换 \(B_{\mathrm{hyp}}\) 复合，得到

\[
H\perp q_R\simeq q_{A_{\mathrm{orig}}},\qquad
x\longmapsto G_S(B_{\mathrm{hyp}}x),
\]

以及同一个参数域上的

\[
C_0(H\perp q_R)\simeq_S C_0(q_{A_{\mathrm{orig}}}).
\]

两者分别由 `incidenceOriginalGenericQuadraticIsometry` 和
`incidenceOriginalGenericEvenCliffordEquiv` 构造。前者的 `_apply` 定理明确保留两次实际坐标变换的次序；后者通过已证明的偶 Clifford 泛性质映射及其生成元公式实现，并保留 \(S\) 的系数作用。统一公共点端点在同一组存在量词下同时给出原矩阵网和归一化矩阵网的这两种比较。

这个归一化比较仍然发生在原五维矩阵网的实际二次空间之间，并不把该五维型直接识别成原题圆锥丛的三维泛纤维型。后者仍须经过下面的 Clifford/Brauer 和实际圆锥比较。

## 6. 剩余的关键比较

本轮没有完成下列步骤：

1. 将 \(C_0(H\perp r)\) 识别为 \(M_2(C_0(r))\)，以及由此推出所需的 Brauer 类比较；
2. 将实际三元偶 Clifford 代数、圆锥的四元数类及原圆锥丛的泛纤维接通；
3. 从原偶 theta 和实际判别覆盖推出所需矩阵网、Brauer 等式及公共实点；
4. 从原题全部假设推出原实点集连通性。

特别地，\(C_0(H\perp r)\simeq C_0(q)\) 不能单独替代第 1 步，也不能用来宣称已经证明原圆锥丛与所构造圆锥的泛纤维同构。当前结果是后续双曲约化所需的实际对象比较，仍不是原题的完整形式化证明。
