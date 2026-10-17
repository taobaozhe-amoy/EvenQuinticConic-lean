# 实际泛纤维与保持参数域的函数域比较

本阶段形式化纸面证明后半段的局部化步骤。对象是此前已经构造的实际全局关联开集及其实际参数投影，不额外假设泛纤维非空、整性、参数拉回单射或函数域同构。

## 精确对象和输入

令 `K` 为无限域，`2 ≠ 0`，`M` 为三个实际对称五阶矩阵。假设存在非零公共各向同性向量，且实际行列式多项式满足 `ProjectiveJacobianCertificate`。该证书已证明等价于代数闭包上的非零向量 Jacobian 条件。

已有端点构造可逆坐标变换、坐标指标 `k,p`、非零消元子式，以及非空整的全局关联开集 `U` 和实际支配投影 `f : U → ℙ²_K`。以下记号均使用这些实际映射：

\[
A=K[T_0,T_1,T_2]/(T_k-1),\qquad
B=\text{所选关联开集的仿射坐标环},
\]

\[
F=\operatorname{Frac}(A),\qquad
S=\operatorname{im}(A\setminus\{0\}\longrightarrow B),\qquad
D=S^{-1}B.
\]

`A → B` 是 `incidenceParameterChartMap`。`incidenceParameterGenericPoint` 是实际复合
`Spec F → Spec A → ℙ²_K`。`GlobalIncidenceOpenGenericFiber` 字面定义为 `f` 与这一态射的范畴论 pullback。

这里使用分式域点的实际基变换；尚未另外构造它与 mathlib 以剩余域定义的 `Scheme.Hom.fiber` 的比较同构。

## 已完成的基变换和函数域比较

`AffineGenericFiberLocalization.lean` 从张量积和局部化的泛性质构造

\[
B\otimes_A F\simeq_B D.
\]

代码同时构造实际仿射概形拉回的同构，并验证两条投影。`IncidenceGenericFiberScheme.lean` 将此结果与原来的全局开图同构、射影参数图开浸入拼接，得到

\[
U\times_{\mathbb P^2_K}\operatorname{Spec}F\simeq\operatorname{Spec}D.
\]

两边到 `U` 及 `Spec F` 的态射分别相容；没有另选一个具有同构坐标环的无关概形来替代原拉回。

`LocalizationFractionField.lean` 证明：若实际 `A → B` 单射且两环为整环，则 `D` 是整环，且

\[
\operatorname{Frac}(D)\simeq\operatorname{Frac}(B).
\]

该同构对每个 `b ∈ B` 保持其像，并在整个 `Frac A` 上与实际参数嵌入交换。随后与已有的实际 Cramer 消元同构复合，得到

\[
\operatorname{Frac}(D)\simeq_K K(u,v,w).
\]

`incidenceGenericFiberFractionFieldEquiv_overParameter` 进一步给出这个同一映射的 `F`-代数版本。右端的 `F`-作用是由原参数投影拉回得到的两个具体有理函数决定的。

**这不声称泛圆锥曲线在 `F` 上有理。** 此处右端是带上述实际嵌入的 `K(u,v,w)`，不能将它改写成 `F(z)`。

组装端点 `exists_integral_genericFiber_of_common_point` 从矩阵网、公共点和几何 Jacobian 证书直接推出：可选取归一化及子式，使实际参数投影支配、实际泛基变换非空且整，其坐标环分式域具有上述 `K`-代数同构。参数拉回单射在内部由既有支配性证明提供。

## 实际概形的泛点茎

`SchemeFunctionFieldIso.lean` 从实际开浸入的 `stalkMap` 及泛点相容性构造函数域同构，并先证明它与正则函数的实际拉回交换。

`IncidenceGenericFiberStalk.lean` 将上述实际概形同构接到这一构造，再用 `Spec D` 的泛点茎是 `D` 的分式域，得到

\[
\mathcal K\!\left(U\times_{\mathbb P^2_K}\operatorname{Spec}F\right)
\simeq_F K(u,v,w).
\]

左端字面使用该 pullback 概形的 `Scheme.functionField`。它的 `F`-作用由实际第二投影的截面拉回、再取泛点 germ 定义；不是为得到代数同构而另行搬运一个标量作用。`K`-作用由同一第二投影再复合 `Spec F → Spec K` 得到，并已与限制标量相容。

`globalIncidenceOpenGenericFiberStalkEquiv_of_geometricJacobian` 和 `globalIncidenceOpenGenericFiberStalkEquiv_overGround_of_geometricJacobian` 分别给出参数域及基域版本，在内部由几何 Jacobian 等输入推导参数拉回单射。整性和非空性的实例同样由已有证明提供，不是新增的外部假设。

## 参数域和实际方程

`IncidenceParameterFieldIdentification.lean` 证明实际参数商环与二元多项式环同构，并将其分式域与实际 Cramer 参数生成子域同构。所有参数多项式的评估、实际泛矩阵及其行列式均与这个同构相容。

同一文件从几何 Jacobian 证书推出实际五次行列式多项式非零，证明其齐次性及去齐次化非零，再推出实际泛矩阵行列式非零。这一非零性不再是输入。

`IncidenceGenericConicNondegeneracy.lean` 随后自动选取非零极化系数，按同一坐标置换和极线消元构造实际三元矩阵 `R=EᵀA(t)E`，推出其对称性及 `det R ≠ 0`。更强的 `exists_incidenceGenericConicMatrix_nondegenerate_affine` 可选取避开当前去齐次坐标的极化主元；它的非零性也在内部推出。这里证明的是具体矩阵非退化性，尚未把它升级为相应圆锥概形的光滑性定理。

另令 `P=K[T₁,T₂]`，`C` 为局部化之前的实际 Segre 关联图商环。`IncidenceGenericFiberPresentation.lean` 对任意 `P`-代数 `R` 构造

\[
R\otimes_P C\simeq_R
R[Y_1,Y_2,Y_3]/(L_R,Q_R).
\]

`L_R,Q_R` 是原来实际关联方程经交换变量和系数映射所得的线性、二次方程；对每个参数坐标、空间坐标和选定子式都有明确的兼容公式。还构造两边在这个实际子式处局部化后的同构。可取 `R=Frac P`，也可取实际参数生成子域。

这项表示定理与前面的拉回定理分别保留了所需映射。随后 [实际圆锥图模块](INCIDENCE_CONIC_CHART.md) 已通过原分母子幺半群、张量积及局部化的比较，将它们接合为同一个实际泛纤维到约化射影三元零点概形的开浸入，以及与其非空像开的同构。

`IncidenceLinearQuotient.lean` 进一步将线性消元提升到实际商环同构。对域 `F` 上的 `L=c+∑aᵢYᵢ`，若 `aᵣ ≠ 0`，则 `affineLinearQuotientAlgEquiv` 构造

\[
F[Y_0,\ldots,Y_n]/(L,Q)
\simeq_F
F[Z_0,\ldots,Z_{n-1}]/(\operatorname{elim}_r Q).
\]

正反映射分别来自实际消元代入与保留坐标的恢复；任意多项式及每个坐标的公式均已证明。不要求第二方程非零、不可约或商环整性。这个接口随后已与实际参数系数、三元二次型的去齐次方程及原子式接合，见 [后续完成范围](INCIDENCE_CONIC_CHART.md)。

## 仍须完成

- 实际泛基变换到约化射影三元零点概形的非空开集比较已完成；整条圆锥概形的光滑性、全局整性及与方程商环的 Proj 构造比较尚未完成。
- 将该圆锥曲线的 Clifford/Brauer 类与原圆锥丛的实际类比较，进而比较函数域。
- 从原题偶 theta 数据得到所用的实对称矩阵网、公共实点及相应 Jacobian 输入；完成实覆盖、符号、纯性和二次型理论等尚缺的连接。
- 将原实点集的连通性结论接入最终的原题 Lean 命题。

整个关联概形不可约性、所选开集在整个关联概形中稠密性，不是本条纸面路线新增的必要目标。当前中间定理均不以目标实点集连通、原簇有理或其与上述模型双有理为输入。
