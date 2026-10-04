# EvenQuinticConic

**部分形式化项目；尚未证明原几何问题的存在性或不存在性。**

本项目尝试核查如下问题的一份候选“不存在性”论证：是否存在光滑射影、几何标准的实圆锥曲线丛
`X → ℙ²_ℝ`，其判别曲线为光滑五次曲线，判别双覆盖对应偶 theta characteristic，且实点集有两个连通分支？

当前已构造实际平面曲线概形、由坐标过渡函数下降得到的实际超平面模层及三个坐标截面，并已证明实际二次截面映射满射和四次限制单射。二次满射适用于无限域上、次数大于一且主理想为素理想的齐次方程；不再要求调用者提供满射性、首一性或坐标选择。

此前接通的**实际概形与实际模层的条件定理**进一步说明：在局部标架及局部配对假设下，两个独立截面迫使 `Θ≅H`；代码还内部推出 `h⁰(H)=3` 和 `Θ` 截面空间有限维，因此偶维数推出每个 `Θ` 截面均为零。这些结论通过真实结构态射、配对、单位延拓和层态射粘合证明。从光滑性推出所需素性与正规性，以及 theta 对象、平方配对和原双覆盖的对应仍待完成；原问题的实几何与连通性结论也尚未形式化。因此，**编译成功不表示原存在性问题已解决，也不验证此前整个非形式化证明**。

## 已形式化的内容

| 模块 | 实际数学内容 | 适用边界与后续步骤 |
| --- | --- | --- |
| `PolynomialDegree` | 非零五次多项式整除次数至多四的 `A*D-B²` 时，该式为零；也给出主理想版本 | 构造曲线的主理想成员关系已由完整齐次核接通 |
| `RankOneFactorization` | 在 GCD 幺半群中由 `AD=B²` 推出 `A=ha², B=hab, D=hb²`，包括退化情形 | 实际线丛比较由后续配对及层粘合模块接通 |
| `ConicClassification` | 不成比例的二次式迫使 `h` 是非零常数、`a,b` 的次数至多一 | 独立实际截面的应用由 `ThetaSectionBridge` 接通 |
| `HomogeneousConics` | 将齐次二次式分解为共同非零常数乘齐次一次式的平方/乘积；接上五次式主理想关系 | 构造曲线的实际限制条件均已提供 |
| `IndependentSquares` | 在代数闭域上的整代数中，线性无关的两个元素的平方仍线性无关 | 实际泛点应用已接通；指定 theta 对象仍需几何输入 |
| `RestrictionModel` | 从实际代数同态、核等于五次式主理想及独立元素的平方/乘积像，推导完整齐次因子分解 | 为几何线丛截面构造满足这些条件的模型 |
| `GradedRestriction` | 实际构造 `Xᵢ ↦ fᵢT`，逐次刻画核；从齐次消失条件识别主理想，证明注入系数扩张保持核 | 构造曲线的完整核现由 `PlaneHomogeneousKernel` 提供 |
| `WeightedRestriction` | 保留公共非零权重 `u`，由三个加权乘积等式推出齐次分解，无须假设 `u` 是平方 | 为指定曲线构造实际乘法配对 |
| `SquareExtension` | 在实际代数闭包中构造平方根及保持原底域线性无关性的多项式模型 | 几何泛点截面的构造；加权路线无需使用此扩域 |
| `FiniteDegreeRestriction` | 仅假设四次齐次式的限制单射，即得到同一个二次式分解，无需完整主理想核 | 构造曲线的实际限制单射及二次式提升均已证明 |
| `GenericCoefficientModel` | 从实际系数、加权乘积与限制条件，得到分解及 `u*(α/a(f))²=c≠0`；支持完整核或仅四次单射两种接口 | 将指定曲线接入已证明的实际模层比较定理 |
| `LocalSquareUnit` | 整闭环的分式域中，正次幂为环内单位的元素来自环内单位；包括加权与商的版本 | 为指定几何线丛构造局部系数恒等式 |
| `GenericPointInjection` | 实际整概形的泛点相等判据、限制相容性，以及整闭仿射开集上的唯一单位延拓 | 从目标光滑曲线提供这些整闭仿射开集 |
| `SheafGluing` | 使用真实层公理粘合截面；同一有理函数的局部单位唯一粘合；局部正次幂为单位推出全局单位 | 为 theta 比值提供相应几何局部数据 |
| `SheafTrivialization` | 构造真实模层态射 `r↦r•s`，由局部单位坐标构造真实模层同构 | 构造指定 theta 模层及它的局部标架 |
| `LocalFrames` | 定义与实际限制映射相容的局部标架；从兼容局部单位截面构造全局生成元及 `O≅M` | 指定 theta 线丛的标架及有理截面 |
| `RationalSectionFrames` | 在实际整概形的整闭仿射覆盖上，从遵守真实过渡关系、正次幂为局部单位的有理系数，构造全局生成元及实际 `O≅M` | 为 `theta⊗O(-1)` 构造这些局部系数和恒等式 |
| `ModuleGenericInjection` | 实际带局部标架的模层全局截面由任一非空标架开集上的泛点系数唯一确定 | 将该接口应用于目标 theta 线丛 |
| `SchemeScalarAction` | 从实际结构态射 `X→Spec K` 构造基域作用、scalar towers 和 `K`-线性泛点映射，保持独立性 | 指定曲线及线丛的实例化 |
| `RankOnePairing` | 实际秩一模的双线性配对等于标架系数乘坐标乘积；实际 tensor map 双射推出该系数是单位 | 提供几何的局部完美配对 |
| `ModulePairing` | 自然双线性配对给出真实截面乘积和共同泛点权重；由全局平方恒等式推导局部单位权重 | 为 theta 平方同构构造实际配对 |
| `ModuleHomGluing` | 粘合相容的实际局部模层态射；局部双射构造全局实际同构 | 实例化目标曲线的局部数据 |
| `FrameComparison` | 非零真实源截面与局部加权平方关系推出实际 `N≅M`；内部推导比较态射的交叠相容性 | 从几何构造局部平方关系 |
| `PairingComparison` | 全局配对恒等式 `μ(s,s)=cν(a,a)`、`a≠0`、单位 `c` 推出实际同构，并把 `a` 送到 `s` | 目标配对、整闭仿射覆盖 |
| `ThetaSectionBridge` | 用实际泛点系数、齐次分解和配对比较，从二次式提升与四次单射得到实际 `Θ≅H` | 构造曲线的限制条件已证明；原题 theta 几何数据仍需构造 |
| `QuadraticSections` | 从三个真实 `H` 截面和实际配对构造齐次二次式的线性截面映射；证明泛点公式；满射性给出真实提升 | 构造曲线的满射性现由 `PlaneQuadraticSurjectivity` 提供 |
| `GlobalSectionDimension` | 实际模层同构诱导基域线性截面等价及维数相等；维数至少二给出两个独立截面 | 将一般结论应用于指定曲线 |
| `ThetaFiniteDimension` | 实际二次截面映射满射使 `T` 被六个截面生成；非零截面配对给出注入，内部推出 `Θ` 截面有限维 | 原题 theta 对象及其实际配对仍需构造 |
| `HyperplaneDimension` | 四次单射使三个坐标截面独立，二次满射使其张成；构造真实基并推出 `h⁰(H)=3` | 构造曲线的两项限制条件均已证明 |
| `ThetaIneffectivity` | 从实际限制条件和局部层数据推出 `h⁰(Θ)≥2⇒Θ≅H`；内部证明维数结论后，偶性推出每个截面为零 | 从光滑平面五次曲线验证全部几何输入 |
| `PlaneQuintic` | 实际齐次主理想、射影消失集和锥商环；在锥分式域及归一化坐标中证明低次齐次限制单射 | 完整分次商的 `Proj` 与另一曲线构造的比较仍是单独工作 |
| `PlaneCurveScheme` | 在实际射影平面中构造 `V(F)` 的约化诱导闭子概形、结构态射、泛点及三个仿射坐标开覆盖；从 `(F)` 素性推出整性 | 从光滑五次曲线条件推出素性与正规性 |
| `GenericPullback`、`ProjectiveGenericChart`、`ProjectiveStalkUnits`、`ProjectiveQuarticRestriction` | 将真实射影图册分式拉回实际曲线函数域；用泛点对应的齐次素理想证明四次限制单射 | 未假设或构造锥函数域与曲线函数域的整体同构 |
| `ProjectiveBaseScalars` | 识别图册常数与实际结构态射诱导的基域作用 | 该识别只涉及常数及归一化坐标 |
| `ProjectiveCoordinateSections`、`PullbackTransition` | 在实际射影开集构造 `Xⱼ/Xᵢ`、交叠单位及 cocycle，并沿实际概形态射拉回 | theta 过渡数据仍需来自指定几何对象 |
| `LineBundleGluing`、`LineBundlePresheaf`、`LineBundleSheaf`、`LineBundleFrames` | 从单位 cocycle 实际构造模层；由真实结构层粘合证明层公理，再显式构造相容局部标架 | 不预设待构造模层已存在；全覆盖时才给出整个概形上的秩一覆盖 |
| `PlaneHyperplaneSheaf` | 构造曲线上的实际超平面模层、三个实际全局截面及局部标架；证明泛点坐标等于归一化射影坐标 | 该构造未直接定义原双覆盖所对应的 theta |
| `LineBundlePairing` | 由 cocycle 相乘构造实际平方模层及自然乘法配对；显式局部 tensor 等价证明每个标架子开上的配对完美，系数为一 | 未声称全局截面的 tensor product 一般等于平方层的全局截面 |
| `PlaneHyperplaneRestriction` | 将真实标架与精确四次单射限制到任意非空图册子开，允许另选 theta 平凡化覆盖 | 不假设 theta 在三个完整标准图册上平凡 |
| `PlaneThetaIneffectivity` | 保留原先显式接收 `h2` 的较低层条件接口；曲线、超平面/平方模层、坐标截面、超平面配对和四次单射均内部提供 | `PlaneThetaVanishing` 已自动提供这里的 `h2`；theta 局部数据及偶性仍是几何输入 |
| `HomogeneousLocalizationSections`、`PlaneMonicModel` | 首一超曲面有限自由基下清分母、两个坐标局部化的交；将实际多元锥商环与迭代多项式首一商环连接 | 这些是后续实际截面满射证明所使用的代数步骤 |
| `PlaneHomogeneousKernel` | 从实际射影 stalk 计算所有齐次次数的限制核；得到保留次数的映射之核为 `(F)`，构造锥商环到 `k(C)[T]` 的注入 | 未将锥分式域等同于曲线函数域 |
| `PlaneChartRepresentatives`、`QuadraticFractionBridge` | 提升实际标准图册正则函数为齐次分式；推导实际平方层截面的权重二过渡关系及相容锥分子 | 此处的提升首先是局部提升 |
| `PlaneLinearChartRepresentatives`、`LinearChartQuadraticSections` | 对任意非零一次式 `L` 构造实际 `Xᵢ/L`，粘合实际 `s/L²` 并获得带精确次数的齐次分子 | 不需构造射影自同构或沿其搬运模层 |
| `HomogeneousCoordinateChoice`、`PlaneCoordinateClearing`、`LinearDenominatorClearing` | 在无限域上实际选择使方程首一的多项式坐标变换，构造锥商环等价；在原锥中清除两条一次式的分母并提取二次代表 | 坐标变换只用于锥上的代数运算 |
| `PlaneQuadraticSurjectivity` | 证明实际 `quadraticSectionMap` 满射：无限域、齐次性、次数大于一及 `(F)` 素性足够 | 不要求光滑性、正规性、预先首一或任何全局提升假设 |
| `PlaneThetaVanishing` | 将已证明的二次满射接入实际五次曲线的偶 theta 截面消失定理；调用者不再提供 `h2` 或 `h4` | 仍须提供正规仿射细化上的 theta 标架、完美平方配对及偶性 |
| `CofactorCover` | 带显式 twist 参数的余子式根属于矩阵核；特征不为二时，含非零根的根集合恰有两点；在显式小行列式关系下构造根 | 判别式符号的几何识别；从余秩推出小行列式关系；覆盖的下降、étale 性与 theta 对应 |
| `IsotropicDimension` | 维数和超过环境维数的子空间有非零交；显式分裂二次型的五维子空间限制各向同性 | 从 Clifford 指数和序得到 Pfister 邻形式并证明分裂 |
| `Incidence` | 非零 `2×2` 小行列式条件下，两条齐次线性方程有唯一规范化解，并给出集合等价 | 非空稠密开集、正则映射、概形同构及实双有理性 |
| `ConnectedComponents` | 实际拓扑连通分支商 `ConnectedComponents X` 在 `ConnectedSpace X` 假设下基数为一 | 为所研究的实代数簇证明该连通性假设 |

特别地，`ConnectedComponents` 中的连通性是**显式假设**；这个模块没有从圆锥曲线丛的几何条件推出连通性。

## 当前接通的证明链

目前最具体的定理是 `planeQuintic_even_theta_sections_eq_zero_of_normal_frames`：对齐次五次式 `F`、`totalDegree F = 5` 且 `(F)` 为素理想，从实际构造的曲线及坐标数据出发，证明每个实际 theta 全局截面为零。剩余输入精确为：

- 代数闭基域；实际模层 `Θ` 及自然平方配对 `μ:Θ×Θ→T`，其中 `T` 是已构造的超平面平方模层。
- 覆盖整个曲线的非空仿射开集 `Vᵢ`，其坐标环整闭；每个 `Vᵢ` 包含于某个标准坐标开，且 `Θ` 在 `Vᵢ` 上有相容局部标架，`μ` 的局部 tensor map 双射。
- 偶性 `Even (finrank K Γ(Θ))`。

曲线的整性、实际 `H,T`、三个截面、超平面配对的局部完美性、实际二次满射及精确四次单射都已由代码提供。代数闭域的无限性也由类型实例提供，不是额外调用条件。覆盖允许细化，**没有假设任意 theta 在三个完整坐标开上平凡**。有限维性和 `h⁰(H)=3` 也在证明内部推出。该定理通过原来的条件接口调用一般实际模层定理 `even_theta_ineffective_of_restriction_maps`，其证明如下。

证明先由满射性提升 `s²,st,t²`，用实际配对推导共同权重，再从 `AD=B²` 得到

$$
A=ca^2,\qquad B=cab,\qquad D=cb^2,\qquad c\ne0.
$$

这给出一个真实非零 `H` 截面及真实全局平方恒等式。局部完美配对提供单位系数，整闭性把平方商延拓成单位，实际局部比较态射再粘合成 `Θ≅H`。同一组限制条件还强制三个坐标截面构成 `H` 截面空间的基；二次满射与非零截面的配对注入则证明 `Θ` 截面有限维。于是两个独立截面会迫使 `h⁰(Θ)=3`，与正偶数维数矛盾。局部权重、交叠相容性、维数和最终同构均在证明中构造。

**几何实例化已有推进，但仍是条件结论。** `PlaneCurveScheme` 构造的是实际 `Proj K[X₀,X₁,X₂]` 内 `V(F)` 的约化诱导闭子概形。素性、齐次性和次数条件给出实际整性、泛点描述及三个非空仿射开覆盖。`LineBundleSheaf` 从 `Xⱼ/Xᵢ` 的单位过渡数据构造真正模层，`PlaneHyperplaneSheaf` 构造其三个真正全局截面；这些截面的泛点系数已与实际射影坐标相连。四次单射通过实际概形态射及泛点素理想证明，常数与结构态射的基域作用也已识别；`planeQuintic_hyperplane_quartic_injective` 给出三个实际全局截面所需的精确 `aeval` 单射形式。

**实际二次截面映射满射的缺口现已补上。** 证明先从实际闭浸入和射影图册同构提升局部正则函数，再在任意一次式图册上粘合 `s/L²`，得到次数精确的齐次分子。完整齐次限制核把分子的泛点相容性变成原锥商环中的等式；实际多项式坐标变换与首一有限自由商环提供两条适当一次式的清分母性质，齐次投影最后提取二次式。实际全局截面的泛点单射证明该二次式确实限制为原截面。首一性与坐标选择都在证明内部取得。

这里没有把整个锥分式域等同于曲线函数域：保留次数的锥嵌入以 `k(C)[T]` 为目标。也没有证明与另一构造 `Proj(K[X₀,X₁,X₂]/(F))` 的概形同构，或使用射影自同构来搬运模层。仍须从目标光滑曲线获得所需素性、正规性和 theta 标架，并从原双覆盖构造 theta 模层及指定平方配对；伴随公式对典范层与超平面平方层的识别也尚待形式化。

[theta 引理的纸面证明与精确形式化边界](docs/THETA_BRIDGE_REVIEW.md) 保留完整数学论证。形式化采取局部单位与实际层同构路线；纸面证明中的除以二只发生在实际除子群中，不能在 Picard 群中这样消去。

[实几何与二次型论证的审查](docs/REAL_OBSTRUCTION_AUDIT.md) 另行核查实双覆盖的 twist、Brauer 类、Albert/Pfister 论证和有理性路线。这是有精确文献依据的非形式化论证，不是 Lean 证书。

余子式方程现在写作 `vᵢvⱼ=twist*adj(M)ᵢⱼ`。正、负两种选择都被支持；代码没有把三阶矩阵的负号约定自动移用于目标五阶矩阵。

## 构建与审计

本版包含 63 个源码模块、382 条公开手写定理，另有 5 条私有辅助定理（共 387 条手写定理）。本地构建和公理审计均通过；审计检查的 932 个声明包含 732 个 theorem 声明，其中包括 Lean 自动生成的声明，不能与手写定理数混同。

环境固定为 Lean `v4.24.0` 和 mathlib 提交
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`。提交的 `lake-manifest.json` 固定传递依赖。

安装 [elan](https://github.com/leanprover/elan) 后，在项目根目录运行：

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

`Audit.lean` 枚举 `EvenQuinticConic` 命名空间内的声明，递归收集其公理依赖；除 Lean/mathlib 常用的 `propext`、`Classical.choice`、`Quot.sound` 外，出现任何公理均使审计失败。这会拒绝 `sorryAx` 及项目自定义公理。审计通过仅保证代码中精确命题的依赖，不能保证它们与非形式化几何论证相同。

GitHub Actions 配置见 `.github/workflows/lean.yml`。其运行相同构建和审计命令。实际本地验证记录见 `verification/`；远程验证以对应提交的 Actions 运行结果为准。

## 后续证明任务

完整论证的缺口列于 [docs/PROOF_GAPS.md](docs/PROOF_GAPS.md)，固定版本 mathlib 的能力检查见 [docs/MATHLIB_STATUS.md](docs/MATHLIB_STATUS.md)。文档中的纸面论证和待办条目不因写入文档而获得 Lean 验证；已验证范围以所引用定理的实际类型和证明为准。

用户提供的参考项目是 [RealConicBundles-Problem3-lean](https://github.com/fanyh27/RealConicBundles-Problem3-lean)。本次对比使用提交 `8b2e7df967727bf82d1c3430128b928e338c31b9`：其 README 明确不附加偶 theta、几何有理性或相对 Picard 秩的要求。进一步，对该提交的具体三阶分次矩阵作余核计算，得到

$$
0\to\mathcal O(-2)^2\oplus\mathcal O(-3)\to\mathcal O(-1)^2\oplus\mathcal O\to i_*\theta\to0,
\qquad h^0(\theta_{\mathbb C})=1.
$$

因此这个具体矩阵对应奇 theta。计算及其与双覆盖的对应见 [实几何审查第 8 节](docs/REAL_OBSTRUCTION_AUDIT.md)。**这是非形式化的奇偶性计算，不是该参考项目或本项目已有的 Lean 定理。** 它与参考项目实际陈述的结论相容。

## English scope note

This repository contains independently checkable lemmas from an attempted obstruction argument for real conic bundles with smooth quintic discriminant and even theta characteristic. It is **not** a formal proof of the geometric obstruction, nor a construction of an example. The remaining geometric obligations are listed explicitly in `docs/PROOF_GAPS.md`. In particular, the final connectedness assumption has not been deduced from the original hypotheses.
