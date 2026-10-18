# 实际泛纤维与射影三元方程开集的比较

本阶段把 [上一阶段](INCIDENCE_GENERIC_FIBER.md) 的实际泛纤维、参数域、方程表示和线性消元接合。目标概形采用项目已有的 `PlaneCurveScheme`：它是实际射影平面中该齐次方程零点集的约化闭子概形。

## 参数域和实际对象

保留原来的矩阵网、公共坐标点及几何 Jacobian 输入，以及已选择的关联图与非零子式。记

\[
A=K[T_0,T_1,T_2]/(T_k-1),\quad F=\operatorname{Frac}(A),\quad
S=\text{实际 Cramer 参数生成子域}.
\]

`incidenceParameterChartFieldEquiv` 构造的同构记为 \(e:F\simeq_K S\)。\(D\) 始终是上一阶段的 `IncidenceGenericFiberRing`；它的 \(S\)-作用是实际结构映射 \(F\to D\) 与 \(e^{-1}\) 的复合。没有将两个参数域静默视作同一个类型。

`IncidenceGenericFiberLocalizationComparison.lean` 证明：改用参数多项式环 \(P=K[t_1,t_2]\) 后，映入原关联坐标环的分母子幺半群保持不变；实际子域 \(S\) 是这个 \(P\) 的分式域。随后通过张量积与局部化的泛性质，比较原 \(D\) 与之前构造的实际基变换方程商环在原子式处的局部化。原坐标和整个参数域映射均被追踪。

## 方程和坐标的一致性

设 \(B(t)\) 为实际五阶泛矩阵，\(p\) 为四个空间齐次坐标中的归一化坐标。选择 \(q\in\mathrm{Fin}(3)\)，令

\[
r=p.\mathrm{succAbove}(q),\qquad s=q.\mathrm{predAbove}(p).
\]

主元 \(r\) 避开 \(p\)。实际线性方程为

\[
L=c+\sum_{j=0}^{2}a_jY_j,
\quad c=B(t)_{p+1,0},\quad
a_j=B(t)_{p.\mathrm{succAbove}(j)+1,0}.
\]

`IncidenceGenericFiberElimination.lean` 先证明基变换后的两条方程字面等于这个 \(L\) 和实际空间二次型的去齐次方程。若 \(a_q\ne0\)，实际消元给出商环同构，并在同一次代入下追踪原子式。

`IncidenceConicDehomogenization.lean` 证明两种坐标处理顺序严格相容：先令 \(y_p=1\) 再消去第 \(q\) 个仿射变量，与先消去齐次变量 \(y_r\) 再令保留的第 \(s\) 个坐标等于一，得到相同的二元多项式。证明在多项式代数同态层面完成，不仅比较域上点的取值。

令

\[
R=E^{\mathsf T}B(t)E,\quad H=\sum_{i,j=0}^{2}R_{ij}Z_iZ_j,
\quad h=\operatorname{dehom}_s(H),
\]

其中 \(R\) 是此前构造的实际三元限制矩阵；令 \(m\) 是原子式经上述同一次消元得到的二元多项式。组装同构的形式为

\[
D\simeq_S \bigl(S[z_0,z_1]/(h)\bigr)_{\bar m}.
\]

这里的局部化元素是原子式的实际像，而非另选的任意非零元素。

## 实际射影图与局部约化性

`PlaneConicAffineChart.lean` 通过真正的射影标准图构造

\[
\operatorname{Spec} S[z_0,z_1]_m\longrightarrow\mathbb P^2_S.
\]

拉回实际闭集 \(V(H)\)，得到局部化理想 \((h)S[z_0,z_1]_m\) 的零点集。利用商与局部化交换，以及已证明的 \(D\) 为整环，推出这个**局部化后的**理想为根理想。于是 `reducedClosedChartMap` 给出实际方程商环的谱到 `PlaneCurveScheme H` 的开浸入。

`IncidenceGenericConicChart.lean` 将上述比较与上一阶段实际泛纤维的谱表示复合，构造实际泛纤维到该射影零点概形的开浸入，以及它与自身非空像开的同构。非空性由实际泛纤维的整性推出，不要求 \(S\)-有理点。

`exists_globalIncidenceGenericConicChart` 在原关联图上内部选择主元，同时给出实际三元矩阵的对称性与行列式非零。`exists_genericConicOpen_of_common_point` 进一步从任意非零公共各向同性向量开始，内部构造可逆归一化矩阵、原关联图和非零子式，再推出上述实际非空开集比较。主元、局部整性或目标同构均不是这一最终端点的输入。

记所构造开浸入为 \(j:U_\eta\to V(H)\)，曲线结构态射为 \(c:V(H)\to\operatorname{Spec}S\)，原泛纤维结构态射为 \(\pi_\eta:U_\eta\to\operatorname{Spec}F\)。参数结构必须满足

\[
c\circ j=\operatorname{Spec}(e^{-1})\circ\pi_\eta.
\]

代码使用具体的概形态射等式核对这一点。

## 仍未由这些结果推出的结论

- 后续 [圆锥几何与函数域](INCIDENCE_CONIC_GEOMETRY.md) 已由非退化矩阵推出全局方程素性、整条实际圆锥概形的整性和光滑性，并比较其实际函数域；没有仅凭一个局部化为整环就推断全局整性。
- 尚未完成 `PlaneCurveScheme H` 与 \(\operatorname{Proj}(S[Z]/(H))\) 的比较，以及实际概形基变换与扩域方程模型的识别。
- 没有宣称圆锥曲线在 \(S\) 上有理，或其函数域为 \(S(z)\)。
- Clifford/Brauer 类与原圆锥丛的比较、原偶 theta 输入到所用矩阵网及公共实点的连接、最终实点连通性结论，仍需形式化。

这些是当前形式化范围的边界，不是最终几何端点的新增假设。
