# 实际圆锥概形在扩域后的整性

本文接续 [圆锥几何与函数域](INCIDENCE_CONIC_GEOMETRY.md)，处理原实际圆锥概形的范畴基变换。通用三元二次型端点及实际关联模型端点均已通过严格模块构建；全项目构建和公理审计结果统一记录在 [核验说明](../verification/README.md)。

## 对象与精确结论

令 `K L : Type` 为域，给定实际系数结构 `[Algebra K L]`。对

\[
H(Z)=\sum_{i,j=0}^{2}M_{ij}Z_iZ_j,
\qquad M=M^{\mathsf T},\qquad \det M\ne0,\qquad 2\ne0,
\]

原对象仍为 `PlaneCurveScheme H`，即原射影平面内的约化闭零点概形。`PlaneCurveFieldBaseChange L H` 字面定义为

\[
C_L=C\times_{\operatorname{Spec}K}\operatorname{Spec}L,
\]

其中两条态射分别为原 `planeCurveStructure H` 和实际 `algebraMap K L` 诱导的 `Spec.map`。目标端点是

```lean
Incidence.ternaryConicFieldBaseChange_isIntegral
  (L := L) h2 M hM hdet :
  IsIntegral (PlaneCurveFieldBaseChange L (matrixQuadraticPolynomial M))
```

结论涉及原概形的实际 pullback，而非仅仅在 `L` 上重新写一个不可约方程。`K L : Type` 是当前实际层与坐标图接口的宇宙限制；在此范围内扩域任意，不要求代数扩张、代数闭、无限域或有理点。原参数域和实数域均属于这个范围。

固定版本的 mathlib 没有 `Scheme.GeometricallyIntegral` 类。本项目直接陈述并证明每个上述扩域的实际基变换为 `IsIntegral`，不以一个不存在的类名表示结果。

## 从实际截面到字面方程

`PlaneCurveAffineEquation.lean` 对正齐次、次数大于一且主理想为素理想的方程 `F`，使用实际坐标比截面构造两变量多项式环到第 `i` 个射影标准开集截面环的映射。它证明该映射满射且核恰为

\[
(\operatorname{dehom}_i F),
\]

进而给出实际概形同构

\[
U_i\simeq\operatorname{Spec}
 K[x_0,x_1]/(\operatorname{dehom}_i F).
\]

变量按 `i.succAbove` 的原次序对应实际坐标比。系数作用由原曲线结构态射拉回，不是为得到同构而另行指定；同构正反方向与结构态射的复合等式均有证明。齐次性、次数大于一及主理想素性共同保证这些标准开非空，字面方程商环为整环。

## 张量积与真正的图基变换

`PlaneEquationBaseChange.lean` 在任意交换环代数 `R → S` 上证明

\[
S\otimes_R\bigl(R[x_0,x_1]/(\operatorname{dehom}_i F)\bigr)
\simeq_S
S[x_0,x_1]/(\operatorname{dehom}_i(\operatorname{map}F)).
\]

此环论步骤不要求约化、素性、平坦性或域假设。扩系数与去齐次化交换；同构保留每个显示的多项式、两个坐标类和系数。右侧张量包含对应商代数上的实际系数映射。

`PlaneCurveChartBaseChange.lean` 将其与实际仿射概形拉回的张量积表示、上一节的实际标准图同构复合，得到

\[
U_i\times_{\operatorname{Spec}K}\operatorname{Spec}L
\simeq
\operatorname{Spec}L[x_0,x_1]/
(\operatorname{dehom}_i(\operatorname{map}F)).
\]

两条投影分别是原图的系数映射和扩域后的结构态射。`planeCurveChartBaseChange_isPullback` 明确证明这个带实际映射的方块是拉回方块。因而扩域方程商环为整环可以用于推出**实际图基变换**的整性。

## 从三个图到整个实际拉回

`PlaneCurveFieldBaseChangeCover.lean` 以三个原标准开集的实际拉回覆盖 `C_L`。每个图的像精确等于第一投影对原标准开的逆像。

仅仅证明覆盖中的每个图整，仍不足以推出整个概形不可约：还须排除互不相交的分支。这里原曲线的泛点位于全部三个标准开中，概形拉回的点存在性定理给出 `C_L` 中一个映到该泛点的点。这个点同时属于全部三个扩域图的像，所以各图的像两两相交。该点的剩余域无需为 `L`；证明不假设圆锥有 `L`-有理点。

`SchemeIntegralOpenCover.lean` 将整图、覆盖和两两相交合并为整体整性。`TernaryConicBaseChange.lean` 则使用此前任意扩域下三元二次方程仍不可约的结果，逐个证明扩域方程图为整，接入上述真实拉回覆盖。

## 与原关联模型的连接

实际关联模型中的参数域仍是先前构造的 Cramer 子域，实际三元矩阵仍来自原五阶泛矩阵及同一次极化消元。相应接口将本结果用于这个实际参数域上的圆锥；所需矩阵对称性、非退化性和特征条件由此前的矩阵网、公共点及几何 Jacobian 证书推出。

`IncidenceGenericConicBaseChange.lean` 的归一化接口为：

- `incidenceGenericConicFieldBaseChange_isIntegral`：对实际参数域的任意上述扩域，原圆锥的实际 pullback 为整概形。
- `incidenceGenericConicFieldBaseChange_isSmoothOfRelativeDimension`：同一 pullback 的实际第二投影光滑、相对维数为一，由原结构态射的光滑性及基变换稳定性推出。

`exists_fieldExtension_integral_smooth_genericConic_of_common_point` 从任意非零公共各向同性向量出发，内部选取归一化矩阵、关联图、非零子式及极化主元。它在同一组存在量词下保留此前的实际参数作用与基域作用、函数域同构、原泛纤维到非空像开的同构，并新增对所选圆锥的任意参数扩域整性；原结构态射的相对维数一光滑性也保留。扩域整性或扩域后的有理点都不是输入。


## 仍未完成

- 尚未粘合一个全局同构，将 `C_L` 识别为 `PlaneCurveScheme (MvPolynomial.map (algebraMap K L) H)`；本轮所用的是保持两条投影的实际标准图比较及覆盖。
- 尚未构造原约化闭子概形与 `Proj(K[Z]/(H))` 的全局同构。
- Clifford/Brauer 类、原圆锥丛的实际识别、偶 theta 与所需矩阵网及公共实点的连接、原实点集连通性仍未完成形式化。

扩域整性不推出参数域上的有理点或有理性，也没有把此前保持实际参数作用的函数域 `K(u,v,w)` 识别成参数域上的一元有理函数域。

## 后续实际 Clifford 比较

[实际双曲分解与偶 Clifford 运输](INCIDENCE_HYPERBOLIC_CLIFFORD.md) 已将同一圆锥的三元型接到原五维泛型的显式双曲分解，并给出实际偶 Clifford 等距运输及归一化比较。矩阵代数约化 `C₀(H⊥r) ≃ M₂(C₀(r))` 和原 Brauer 类比较仍未完成。
