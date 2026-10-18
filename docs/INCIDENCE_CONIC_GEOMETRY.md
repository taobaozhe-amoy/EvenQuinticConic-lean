# 实际圆锥概形的整性、光滑性与函数域

本阶段继续 [实际圆锥图比较](INCIDENCE_CONIC_CHART.md)。先前已经将原泛纤维识别为实际射影三元零点概形的非空开集；本阶段证明整条目标概形的性质，并将函数域比较延伸到它的实际泛点茎。

## 对象与输入

沿用无限域 `K`、`2 ≠ 0`、实际对称五阶矩阵网、公共点以及实际行列式的几何 Jacobian 证书。归一化后，关联图上的非零子式决定实际参数子域 `S ⊂ K(u,v,w)`。在一个有效极化主元处消元，得到同一实际三元对称矩阵 `R` 和齐次方程

\[
H(Z)=\sum_{i,j=0}^{2}R_{ij}Z_iZ_j.
\]

`C = IncidenceGenericConicScheme ...` 仍是先前的 `PlaneCurveScheme H`，即实际射影平面零点集的约化闭子概形。没有换用另一个假定同构的抽象圆锥。

`incidenceGenericConicMatrix_det_ne_zero_of_geometricJacobian` 对任意有效主元，从原泛矩阵的行列式非零推出 `det R ≠ 0`。此前已构造有效主元的存在性。

## 方程不可约与概形整性

`TernaryConicIrreducibility.lean` 在任意特征不为二的域上证明非退化对称三元二次式不可约。证明步骤是：

1. 实际 Hessian 等于 `2R`，故方程非零且总次数恰为二。
2. 非平凡分解可齐次化为正次数因子；次数相加等于二，故其中因子为齐次一次式。
3. 一次式乘任意多项式在原点的 Hessian 是两个外积之和，其三阶行列式为零。
4. 与 `det(2R) = 2³ det R ≠ 0` 矛盾。

由不可约性得到实际主理想 `(H)` 为素理想。`incidenceGenericConicScheme_isIntegral` 将素性、齐次性及次数接入原实际射影概形，推出 `IsIntegral C`。这里没有用单个局部化整环的性质替代全局证明。

另证明对每个域同态 `f : S →+* L`，字面扩系数多项式 `MvPolynomial.map f H` 仍不可约，其主理想仍为素理想。这是多项式层面的绝对不可约性；实际概形基变换比较的边界见下文。

## 实际结构态射的光滑性

`TernaryConicGradient.lean` 证明更强的理想论断：若某个理想包含全部偏导，它也包含全部坐标变量。证明将偏导公式 `∇H = 2RZ` 放入商环，并使用可逆矩阵作用的单射性。因此每个实际射影素点上至少有一个偏导不在该点的齐次素理想中。

`TernaryConicSmooth.lean` 将此前五次曲线的实际仿射图论证扩展到任意正齐次次数。非径向偏导给出的主开集覆盖实际曲线；每个主开上的实际截面环与原系数映射具有相对维数一的标准光滑表示。由覆盖得到实际结构态射光滑。

`incidenceGenericConicStructure_isSmoothOfRelativeDimension` 将其用于原实际矩阵，得到

\[
C\longrightarrow\operatorname{Spec}S
\quad\text{光滑，相对维数为 }1.
\]

无需假设代数闭、有理点或目标光滑性；证明检查所有射影素点，不只是基域上的向量。此光滑接口的 `K : Type` 宇宙限制来自既有层与坐标图接口，包含本题所用的实数域及实际参数子域。

## 整条概形的实际函数域

`IncidenceGenericConicFunctionField.lean` 使用已构造的实际开浸入

\[
U_\eta\longrightarrow C
\]

在泛点处诱导的茎映射，再复合此前原泛纤维的实际函数域比较（该比较通过 `U_η ≅ Spec D` 和分式域局部化构造），得到

\[
\mathcal K(C)\simeq_S K(u,v,w).
\]

左边是 mathlib 的实际 `Scheme.functionField`。其 `S` 作用由曲线结构态射拉回常数，再取泛点 germ 定义；右边是实际 Cramer 子域的包含。独立模块 `IncidenceSpatialParameterComparison.lean` 中的 `incidenceSpatialParameterAlgebra_eq_actual` 比较整个参数分式域上的映射。`incidenceGenericConicFunctionFieldRingEquiv_parameter` 证明每个参数常数都被送到其实际 Cramer 值。

基域作用同样由实际复合结构态射 `C → Spec S → Spec K` 定义，并证明它是上述参数作用的限制。两个最终接口为：

- `incidenceGenericConicFunctionFieldEquiv_overParameter_of_geometricJacobian`；
- `incidenceGenericConicFunctionFieldEquiv_overGround_of_geometricJacobian`。

它们内部推导目标整性，不要求额外输入整性、参数拉回单射或函数域同构。底层通用比较保留整性实例参数，是为了复用泛点接口；上述最终接口已经消去这个独立输入。

## 从任意公共点出发的组装定理

`exists_integral_smooth_genericConic_of_common_point` 从原对称矩阵网、任意非零公共各向同性向量和几何 Jacobian 证书出发，内部选择可逆归一化矩阵、关联图、非零子式和极化主元。输出同一个实际圆锥概形的整性、相对维数一的光滑性、参数域与基域两个版本的实际函数域同构，以及原泛纤维到其非空像开的实际开浸入和同构。这些性质和比较均不是定理输入。

## 尚未完成的连接

- 该实际约化闭子概形与 `Proj(S[Z]/(H))` 的概形同构。
- 实际范畴基变换与扩系数方程模型的识别。因此本阶段没有宣称已经构造 mathlib 的 `Scheme.GeometricallyIntegral` 证书。
- Clifford/Brauer 类及原圆锥丛的比较。
- 原题偶 theta、指定实判别覆盖、矩阵网及公共实点之间的全部连接，以及最终实点连通性。

这里的函数域同构没有把 `K(u,v,w)` 改写为 `S(z)`，没有声称圆锥在参数域上有理。`C` 在 `S` 上是一条曲线；上述域同构也没有将其复合到 `K` 的态射认定为有限型三维有理簇。
