# EvenQuinticConic

**部分形式化项目；尚未证明原几何问题的存在性或不存在性。**

本项目尝试核查如下问题的一份候选“不存在性”论证：是否存在光滑射影、几何标准的实圆锥曲线丛
`X → ℙ²_ℝ`，其判别曲线为光滑五次曲线，判别双覆盖对应偶 theta characteristic，且实点集有两个连通分支？

当前已构造实际平面曲线概形、由坐标过渡函数下降得到的实际超平面模层及三个坐标截面，并已证明实际二次截面映射满射和四次限制单射。二次满射适用于无限域上、次数大于一且主理想为素理想的齐次方程；不再要求调用者提供满射性、首一性或坐标选择。

最新定理 `planeQuintic_even_theta_sections_eq_zero_of_jacobian` 直接从齐次五次方程的 Jacobian 非奇异条件出发，内部推出方程不可约与主理想素性、实际曲线结构态射的相对维数一光滑性，以及正规性。图册的完整关系理想 `(F, Xᵢ−1)`、偏导主开覆盖与标量兼容性均已证明。实际线层的局部平凡化和平方同构再提供所需标架与完美配对，最终偶维数推出截面消失。

本轮补充实际微分层及其普适性质、规范仿射比较同构、微分预层在真实偏导主开集上的坐标基，以及五次曲线留数微分的局部过渡恒等式。这些构造使用同一个实际结构态射给出的基域作用。局部微分模的基尚未搬运成曲线上微分层的局部平凡化；全局伴随同构仍是待证目标。

该定理仍接收指定线层的局部平凡化、平方同构及截面维数偶性。伴随公式、原判别式双覆盖与 theta 的对应、从实数据到代数闭域的基变换，以及实几何和连通性结论尚未形式化。因此，**编译成功不表示原存在性问题已解决，也不验证此前整个非形式化证明**。

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
| `PlaneCurveScheme` | 在实际射影平面中构造 `V(F)` 的约化诱导闭子概形、结构态射、泛点及三个仿射坐标开覆盖；从 `(F)` 素性推出整性 | 这两项已由后续 Jacobian 模块从原始多项式非奇异条件推出 |
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
| `LocalTrivializationFrames`、`FrameCocycleDescent` | 实际局部单位层同构与相容标架双向转换；构造单位 cocycle 及原层与下降层的实际同构 | 原双覆盖所指定的线层仍需构造 |
| `AffineCommonRefinement`、`NormalSchemeSections` | 从两个开覆盖选择非空共同仿射细化；由实际 stalk 整闭性推出仿射截面环整闭 | 不要求 theta 在整个标准坐标开上平凡 |
| `LineBundleSquareIso`、`LineBundleTensorUniversal` | 由实际平方层同构构造局部完美配对；证明乘积 cocycle 层对自然双线性配对的真正张量泛性质，并沿实际层同构传递 | 不把全局截面的张量积等同于张量层的全局截面 |
| `SmoothCurveNormality`、`SmoothSchemeNormality` | 由余切单射、微分模基变换和极大局部化证明一维标准光滑整代数整闭；推出完美域上实际光滑整曲线的 stalk 与非空仿射截面环整闭 | 整性及相对维数一的实际光滑态射条件仍明确给定 |
| `PlaneThetaLineBundle`、`PlaneThetaSmooth` | 对给定实际局部平凡 theta 层及平方同构证明偶维截面消失；正规性、细化、标架、配对及其完美性均内部构造 | 仍需原双覆盖、伴随公式及后续实几何桥梁 |
| `ChartHomogenization`、`PlaneChartPolynomialMap` | 构造齐次化，证明实际图册多项式映射满射，完整核恰为 `(F,Xᵢ−1)`，并识别原结构态射的基域标量 | 核包含非齐次关系；不以函数域模型替代实际图册 |
| `JacobianLocalization`、`PlaneJacobianPresentation`、`PlaneGradientCover`、`PlaneJacobianSmooth` | 构造有限表示，计算偏导 Jacobian，反演偏导后得到标准光滑图册，再由实际主开覆盖证明结构态射光滑 | Euler 步骤不除以次数，适用于特征 5 |
| `HomogeneousFactors`、`PlaneOriginHeight`、`HomogeneousCommonZero` | 最高齐次分量乘法、原点素理想高度至少 3；由 Nullstellensatz 与 Krull 高度定理证明两个正次齐次三元式有非零公共零点 | 明确使用代数闭域 |
| `ProjectiveJacobianPoints`、`ProjectiveJacobianCriterion`、`JacobianIrreducible` | 构造非零向量对应的实际射影点；证明两种梯度条件等价，并推出方程不可约及主理想素性 | 条件检查原始方程，不是仅检查约化零集 |
| `PlaneThetaJacobian` | 从显式多项式 Jacobian 条件接通 theta 截面消失定理，内部推出素性与实际光滑性 | theta 的几何来源、伴随公式和原实问题仍待完成 |
| `SchemeKaehlerSheaf` | 对实际 `X → Spec K` 构造微分预层、层化和普适导子，证明目标模层上的导子与层态射一一对应 | 不把任意开集上的微分层截面等同于该截面环的微分模 |
| `LocalizedModuleStalk`、`AffineKaehlerPresheafLocalization` | 从真实主开集局部化证明真实茎局部化；将其应用于实际微分预层 | 泛用转移引理的局部化输入在仿射微分情形得到证明 |
| `AffineKaehlerDerivation`、`AffineKaehlerComparison` | 通过实际局部分式导子构造到关联模层的规范比较，并通过真实茎与局部双射证明该比较是同构，且保持实际正则函数的微分 | 搬运到曲线的实际仿射开子概形及限制相容仍需接通 |
| `PlaneKaehlerFrames`、`PlaneCurveKaehlerFrames` | 计算偏导主开集上的实际微分模基，并识别唯一基向量为剩余坐标比的微分；显式对齐实际基域作用 | 目前目标是微分预层在该开集上的值，尚非层化后的局部层同构 |
| `PlaneDifferentialIdentities`、`PlaneResidueTransition`、`PlaneResidueCrossTransition` | 实际普适导子的链式法则、曲线微分关系、同图册留数换元，以及两类跨图册坐标缩放下的二次留数恒等式 | 仍须在所有真实开集交叠上组织有符号标架并粘合 |
| `CofactorCover` | 带显式 twist 参数的余子式根属于矩阵核；特征不为二时，含非零根的根集合恰有两点；在显式小行列式关系下构造根 | 判别式符号的几何识别；从余秩推出小行列式关系；覆盖的下降、étale 性与 theta 对应 |
| `IsotropicDimension` | 维数和超过环境维数的子空间有非零交；显式分裂二次型的五维子空间限制各向同性 | 从 Clifford 指数和序得到 Pfister 邻形式并证明分裂 |
| `Incidence` | 非零 `2×2` 小行列式条件下，两条齐次线性方程有唯一规范化解，并给出集合等价 | 非空稠密开集、正则映射、概形同构及实双有理性 |
| `ConnectedComponents` | 实际拓扑连通分支商 `ConnectedComponents X` 在 `ConnectedSpace X` 假设下基数为一 | 为所研究的实代数簇证明该连通性假设 |

特别地，`ConnectedComponents` 中的连通性是**显式假设**；这个模块没有从圆锥曲线丛的几何条件推出连通性。

## 当前接通的证明链

目前最具体的定理是 `planeQuintic_even_theta_sections_eq_zero_of_jacobian`。输入精确为：

- 代数闭基域、齐次五次式 `F`，且 `totalDegree F = 5`。
- 原始方程的 Jacobian 条件：对每个非零向量 `v : Fin 3 → K`，若 `F(v)=0`，则至少一个偏导 `∂ᵢF(v)≠0`。
- 实际模层 `Θ`、一个开覆盖 `Uᵢ`，以及每个 `Uᵢ` 上到单位层的实际同构。覆盖成员无须预先仿射或非空。
- 由这些平凡化构造的平方 cocycle 层到 `PlaneCurveQuadraticSheaf F` 的实际同构。代码证明该平方层表示 `Θ×Θ` 到任意模层的自然双线性配对。
- 偶性 `Even (finrank K Γ(Θ))`。

方程的素性、实际曲线的整性、光滑性与正规性、实际 `H,T`、三个截面、共同仿射细化、theta 标架与完美配对、实际二次满射及精确四次单射都已由代码提供。**没有假设任意 theta 在三个完整坐标开上平凡**。有限维性和 `h⁰(H)=3` 也在证明内部推出。较低层的素性、光滑态射及正规标架接口仍保留。最终定理调用一般实际模层定理 `even_theta_ineffective_of_restriction_maps`，其截面论证如下。

证明先由满射性提升 `s²,st,t²`，用实际配对推导共同权重，再从 `AD=B²` 得到

$$
A=ca^2,\qquad B=cab,\qquad D=cb^2,\qquad c\ne0.
$$

这给出一个真实非零 `H` 截面及真实全局平方恒等式。局部完美配对提供单位系数，整闭性把平方商延拓成单位，实际局部比较态射再粘合成 `Θ≅H`。同一组限制条件还强制三个坐标截面构成 `H` 截面空间的基；二次满射与非零截面的配对注入则证明 `Θ` 截面有限维。于是两个独立截面会迫使 `h⁰(Θ)=3`，与正偶数维数矛盾。局部权重、交叠相容性、维数和最终同构均在证明中构造。

**几何实例化已有推进，但仍是条件结论。** `PlaneCurveScheme` 构造的是实际 `Proj K[X₀,X₁,X₂]` 内 `V(F)` 的约化诱导闭子概形。素性、齐次性和次数条件给出实际整性、泛点描述及三个非空仿射开覆盖。`LineBundleSheaf` 从 `Xⱼ/Xᵢ` 的单位过渡数据构造真正模层，`PlaneHyperplaneSheaf` 构造其三个真正全局截面；这些截面的泛点系数已与实际射影坐标相连。四次单射通过实际概形态射及泛点素理想证明，常数与结构态射的基域作用也已识别；`planeQuintic_hyperplane_quartic_injective` 给出三个实际全局截面所需的精确 `aeval` 单射形式。

**实际二次截面映射满射的缺口现已补上。** 证明先从实际闭浸入和射影图册同构提升局部正则函数，再在任意一次式图册上粘合 `s/L²`，得到次数精确的齐次分子。完整齐次限制核把分子的泛点相容性变成原锥商环中的等式；实际多项式坐标变换与首一有限自由商环提供两条适当一次式的清分母性质，齐次投影最后提取二次式。实际全局截面的泛点单射证明该二次式确实限制为原截面。首一性与坐标选择都在证明内部取得。

这里没有把整个锥分式域等同于曲线函数域：保留次数的锥嵌入以 `k(C)[T]` 为目标。图册的完整商环表示现在已证明，但尚未构造与 `Proj(K[X₀,X₁,X₂]/(F))` 的显式全局同构。仍须从原实圆锥曲线丛及其判别双覆盖构造方程、复化数据、theta 模层、局部平凡化及指定平方同构；伴随公式对典范层与超平面平方层的识别也尚待形式化。


**原始方程与约化零集必须区分。** `F=X₀^5` 的约化射影零集是光滑直线，但 `(F)` 并非素理想；因此仅凭约化曲线光滑不能删去原方程的素性假设。新定理使用实际偏导值的 Jacobian 条件，该条件排除了这一退化。不可约性证明先用零点定理与高度定理证明两个正次齐次因子必有非零公共零点，再在该点用乘积求导得到所有偏导为零的矛盾。

实际光滑性证明将每个图册表示为三个生成元、两个关系 `(F,Xᵢ−1)` 的商环。选择 `j≠i`，对应 Jacobian 为 `∂ⱼF`；反演其实际截面得到标准光滑的相对维数一代数。Euler 恒等式保证这些偏导主开集覆盖曲线。所有表示、局部化、覆盖与结构态射的标量比较均由代码证明。

[theta 引理的纸面证明与精确形式化边界](docs/THETA_BRIDGE_REVIEW.md) 保留完整数学论证。形式化采取局部单位与实际层同构路线；纸面证明中的除以二只发生在实际除子群中，不能在 Picard 群中这样消去。

[实几何与二次型论证的审查](docs/REAL_OBSTRUCTION_AUDIT.md) 另行核查实双覆盖的 twist、Brauer 类、Albert/Pfister 论证和有理性路线。这是有精确文献依据的非形式化论证，不是 Lean 证书。

余子式方程现在写作 `vᵢvⱼ=twist*adj(M)ᵢⱼ`。正、负两种选择都被支持；代码没有把三阶矩阵的负号约定自动移用于目标五阶矩阵。

## 构建与审计

本版包含 96 个源码模块、541 条公开手写定理，另有 6 条私有辅助定理（共 547 条手写定理）。本地整体构建及公理审计均已通过；完整计数和记录见 `verification/summary.json`。审计包含 Lean 自动生成的声明，不能与手写定理数混同。

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
