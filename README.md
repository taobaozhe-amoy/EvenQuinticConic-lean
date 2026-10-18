# EvenQuinticConic

**部分形式化项目；原几何命题尚未完成 Lean 证明。**

最新形式化已证明：此前构造的实际泛圆锥在任意参数扩域后，其范畴论 pullback 仍为整概形，扩域后的实际结构态射仍光滑且相对维数为一。证明先把三张实际仿射图识别为去齐次方程商环，再构造保持两个投影的基变换同构，最后通过有公共概形点的开覆盖推出整体整性。最终端点从原矩阵网、公共点和几何 Jacobian 条件内部导出所需非退化性及扩域素性，保留原参数与基域作用下的函数域同构；没有额外假设扩域整性或圆锥有理点。概形接口目前使用 `K L : Type`（宇宙零）。**原题连通性结论尚未完成 Lean 证明，也没有宣称泛圆锥在参数域上有理。** 见 [实际扩域与整性](docs/CONIC_FIELD_BASE_CHANGE.md)、[圆锥几何与函数域](docs/INCIDENCE_CONIC_GEOMETRY.md)。

[2026-10-17 理论证明与依赖核查](docs/THEORETICAL_PROOF_REVIEW_2026_10_17.md)：补全限制分辨率的 Tor 项、实际实覆盖的乘法与符号、Brauer 常数差、所有排序上的不定性、Albert–Pfister 计算以及 CT–Levine 的约化指数。后半段改为直接比较支配开集的实际泛纤维和函数域，无须先证明整个关联概形不可约。按明确的圆锥丛约定，纸面论证推出实有理性和实点连通性；外部定理均标注准确位置。这是理论推导和审查，不是新增完整 Lean 证书。

[2026-10-16 再次核查](docs/RECHECK_2026_10_16.md)：逐项检查纸面论证及其文献输入，未发现致命错误；同时计算了用户所给双连通分支例子的 theta 为 odd（该奇偶性计算尚未形式化）。新代码从实际行列式 Jacobian 条件推出公共点处极化形式独立，构造实际齐次坐标代换，并将三元二次式分裂成不同直线与负余子式平方严格对应。此前“已经完全证明，只差形式化”的表述应以此处列明的证明边界为准。

进一步已将任意公共非零点的可逆矩阵坐标变换、行列式及偏导的传递、极化独立性、公共因子排除和非零子式组合成同一个 Lean 端点。它直接接收实际对称矩阵网、公共点和实际 Jacobian 条件，输出非零子式的实际取值见证；[精确输入输出与剩余边界](docs/NET_BASEPOINT_AND_SPLITTING.md)。

2026-10-16 新增了行列式实际偏导到非零余子式、对称奇异矩阵的余子式平方关系、实 Kummer 代数的符号分类，以及关联簇局部方程的商环和仿射概形同构。此前的余子式秩一恒等式输入已被推导消去；关联簇部分已超出集合层面的公式。精确命题与剩余几何连接见 [实余子式与关联簇进展](docs/REAL_COFACTOR_AND_INCIDENCE.md)。最终实连通性定理仍未完成形式化。

[当前正确性边界与未完成原因](docs/PROOF_STATUS.md)：已检查的条件性定理不等于原题的完整证明；剩余形式化工作既包括文献输入，也包括自有几何连接论证及原对象的识别。

[偶 theta 与实连通性的纸面论证](docs/EVEN_THETA_CONNECTEDNESS_PROOF.md) 记录了补全细节并列明文献输入的直接论证：实际实双覆盖及 Brauer 类比较、五维二次型各向同性、实关联簇有理模型，以及不依赖解消的连通性证明。它明确引用外部数学定理，尚非完整 Lean 证书；形式化状态不因此改为完成。

本项目尝试核查如下问题的一份候选“不存在性”论证：是否存在光滑射影、几何标准的实圆锥曲线丛
`X → ℙ²_ℝ`，其判别曲线为光滑五次曲线，判别双覆盖对应偶 theta characteristic，且实点集有两个连通分支？

当前已构造实际平面曲线概形、由坐标过渡函数下降得到的实际超平面模层及三个坐标截面，并已证明实际二次截面映射满射和四次限制单射。二次满射适用于无限域上、次数大于一且主理想为素理想的齐次方程；不再要求调用者提供满射性、首一性或坐标选择。

一般 theta 定理 `planeQuintic_even_theta_sections_eq_zero_of_cotangent_square` 直接接收实际线层的平方到真实相对微分层的同构。齐次五次方程的 Jacobian 条件在内部提供素性、光滑性、正规性和伴随同构 `Ω¹(C/K) ≅ PlaneCurveQuadraticSheaf F`；实际线层的局部平凡化和平方同构提供配对，偶维数最终推出每个截面为零。

已完成实际微分层的开子概形限制与仿射图册搬运，把已计算的微分模基接成曲线上的真实局部层标架。偏导逆单位及排列符号给出实际留数标架；全部交叠公式（包括混合偏导情形）与超平面平方 cocycle 一致，粘合后得到 `planeQuinticAdjunctionIsoOfJacobian`。全程使用原结构态射的基域作用，没有把任意开集上的微分层截面等同于截面环的微分模。

该定理仍接收指定线层的局部平凡化、平方同构及截面维数偶性。原判别式双覆盖与指定 theta 的对应、其平方及偶性的几何来源、从实数据到代数闭域的基变换，以及实几何和连通性结论尚未形式化。因此，**编译成功不表示原存在性问题已解决，也不验证此前整个非形式化证明**。


上一阶段新增 `planeQuintic_even_twoTorsion_twist_sections_eq_zero`：输入任意开覆盖上的实际单位 cocycle `g`、其下降线层 η 的实际平方平凡化，以及构造所得扭曲的截面维数偶性。内部构造 Θ=η⊗H，证明对原始两个层的 tensor 普遍性质，并构造 Θ²≅H²≅Ω¹(C/K)。不再额外输入 Θ、Θ 的局部平凡化或 Θ² 到微分层的同构。这里二挠意为阶整除 2，允许平凡线层。

仍未从原题指定的有限 étale 判别式双覆盖提取 η 及其平方平凡化；偶性仍是输入。因此该构造并未完成原实圆锥曲线丛问题。


上一阶段已证明 mathlib 显式二次代数 `QuadraticAlgebra R u 0` 的真实迹零模、乘法张量平方同构及换坐标公式，见 [局部 Kummer 桥梁](docs/LOCAL_KUMMER_BRIDGE.md)。

本轮新增 `planeQuintic_even_trace_kernel_twist_sections_eq_zero`：给定实际模层及限制相容的二次代数图册，内部粘合实际局部代数迹，取其范畴论核层，构造核层标架、单位 cocycle、下降同构及平方平凡化。核层平方配对已证明在每个图上等于原代数乘法；扭曲的 tensor 普遍性质直接作用于这个实际核层。**不再要求输入迹态射、迹核线层的 cocycle 或全局平方同构，但图册与截面维数偶性仍是输入。** 从指定有限 étale 判别双覆盖构造图册、识别其推前层和迹，以及实几何部分仍未完成。精确接口见 [全局迹核桥梁](docs/GLOBAL_TRACE_KERNEL_BRIDGE.md)。

进一步新增 `exists_unit_kummer_model_of_basis`：从实际代数的基 `(1,e)`、`2` 可逆性和 mathlib 的实际形式非分歧性，构造单位参数的 Kummer 代数同构。参数可逆性通过到 `R/(u)` 的导子与真实微分模的普遍性质证明，不是输入假设。`exists_trace_kernel_tensor_equiv_of_basis` 进而构造原代数实际迹核的乘法张量平方同构。**指定双覆盖上的局部基及其限制相容性仍待构造**；见 [有基非分歧二次代数模型](docs/BASED_UNRAMIFIED_QUADRATIC_MODEL.md)。

上一阶段局部环接口 `exists_unit_kummer_model_of_local_finite_flat` 进一步消去全部基输入：对局部交换环上的有限平坦秩二代数，在 `2` 可逆及形式非分歧条件下，内部先推出自由性，再用 `Tr(1)=2` 构造以 `1` 为首项的基，最后得到单位 Kummer 模型。实际迹核的一维坐标及与乘法一致的张量平方同构也已证明。这是局部环上的结论；新的主开集结果见下文。 见 [局部环秩二模型](docs/LOCAL_RANK_TWO_MODEL.md)。

上一阶段新增 `exists_principal_unit_kummer_cover`：从实际交换代数的模有限表示、平坦性、形式非分歧性、`2` 可逆及每个素点处的秩二条件，构造 `Spec R` 的主开覆盖，并在每个主开集上给出实际基变换代数的单位 Kummer 同构。关键改进是以归一化迹完成幺模列，证明任意底环上的秩二基都可改为 `(1,e)`，再结合有限表示模的基延拓定理。主开模型已构造；新的限制与交叠进展见下文。 精确输入见 [主开覆盖模型](docs/PRINCIPAL_OPEN_KUMMER.md)。

上一阶段构造了 Kummer 模型的实际基变换同构，证明坐标、真实代数迹及交叠单位的限制公式。`principalOpenKummerSectionModel` 将主开模型延伸到任意子开集 `V` 的实际结构层截面环 `Γ(V,O)`；两个坐标与所有进一步限制相容。交叠同构经共同代数构造，过渡单位的平方关系、cocycle 及基变换公式均已证明。该阶段的模型定义域为 `Γ(V,O)⊗[R]A`；新的实际推前层比较见下文。 见 [模型限制与结构层系数](docs/KUMMER_MODEL_RESTRICTIONS.md)。

本轮新增 `exists_affinePushforwardKummerAtlas`：对仿射态射 `Spec A → Spec R`，从模有限表示、平坦、形式非分歧、`2` 可逆和逐点秩二条件，构造**实际推前模层 `π_*O` 的覆盖性 `KummerModuleAtlas`**。代码先构造自然张量到实际截面的环映射，在主开集上用局部化证明双射，再用两个坐标的粘合证明任意子开集上的双射；实际标量作用、乘法、限制和交叠均已接通。无需输入图册、截面比较同构或交叠相容性。**仍须将题目指定双覆盖在一般底概形上的仿射局部数据与此构造识别，完成全局迹及 theta、偶性和实几何部分。** 见 [实际仿射推前图册](docs/AFFINE_PUSHFORWARD_ATLAS.md)。

上一阶段补上一般底概形的桥梁：`schemePushforwardRestrictionIso` 证明实际结构层推前与开限制的典范同构；`KummerModuleAtlas.openImage` 将开子概形图册运输回原概形。`PushforwardKummerChart` 保留实际截面环乘法，由同一截面环构造交叠代数同构；`pushforwardKummerAtlas_trace_independent` 证明不同覆盖图册粘出的全局迹相同。`exists_affinePreimageKummerAtlas` 从有限、étale、显式平坦性、Noetherian、2 可逆和秩二条件构造实际截面代数上的仿射图册。**该阶段尚未完成乘法坐标运输；本轮的一般构造见下文，指定双覆盖的实例化仍待完成。** 见 [一般底概形与推前层](docs/GENERAL_BASE_PUSHFORWARD.md)。

本轮新增 `exists_schemePushforwardKummerCharts_of_affine_cover`：从实际态射的有限、étale、显式平坦性，以及仿射覆盖截面环的 Noetherian、2 可逆和局部秩二条件，构造**原底概形上、原态射的覆盖性乘法 Kummer 图册**。沿典范仿射表示运输时完整保留截面环乘法、系数与限制；跨仿射片的交叠由共同实际截面环构造。进一步构造唯一的实际层迹 `schemeFiniteEtaleTrace`、其真正的核层及覆盖性秩一标架；核层平方配对局部张量完美，并证明经真实核包含映射后等于原截面环乘法。**不再输入图册、迹、核层标架或平方配对。** 原题指定判别双覆盖的实例化、theta 对应与偶性、实基变换和连通性仍未完成。见 [几何推前图册与迹核](docs/GEOMETRIC_PUSHFORWARD_TRACE.md)。

## 已形式化的内容

最新接口 `planeQuintic_even_finiteEtale_theta_sections_eq_zero` 已把一般几何迹核接到实际平面五次曲线的 theta 扭曲：调用者提供真实有限 étale 态射、显式平坦性、标准坐标开上的逐点秩二、五次方程的 Jacobian 条件，以及构造层的偶性。图册、迹核、线层下降、平方同构及扭曲均内部构造；坐标环 Noetherian 性与所有开集上 2 可逆由基域推出。另证明不同仿射覆盖构造的迹相等，核层同构保持原包含且唯一。**这仍未把原题指定判别覆盖与构造对象识别，也没有证明原实点集连通。** 原题已有的偶性需要沿该识别及实到复的基变换传递。精确说明见 [几何迹核与 theta 接口](docs/GEOMETRIC_PUSHFORWARD_TRACE.md)。

| 模块 | 实际数学内容 | 适用边界与后续步骤 |
| --- | --- | --- |
| `PlaneCurveAffineEquation` / `PlaneEquationBaseChange` / `PlaneCurveChartBaseChange` | 实际标准图的完整方程商环；扩域张量同构及真实拉回比较，保持两个投影 | 标准图比较使用齐次素方程、次数大于一及宇宙零域 |
| `SchemeIntegralOpenCover` / `PlaneCurveFieldBaseChangeCover` / `TernaryConicBaseChange` | 实际开覆盖与公共点推出整体整性；非退化三元圆锥在任意宇宙零扩域后实际拉回为整概形 | 扩域素性及商环整性均内部推导；无需有理点 |
| `IncidenceGenericConicBaseChange` | 从原公共点数据构造在所有参数扩域后仍整的实际泛圆锥，保留此前光滑性、函数域及开浸入结论 | 扩域后的实际投影亦证明光滑；原圆锥丛比较及实连通性仍未接通 |
| `SchemeFiniteEtaleTraceChoice` | 不同仿射覆盖构造的迹相等；实际核层的规范同构保持包含且唯一 | 各覆盖仍须满足明确的几何及局部秩条件 |
| `SchemeFiniteEtaleData` | 从已证存在性选择实际乘法覆盖，构造规范迹核的下降同构及平方平凡化 | 选择的是已证存在对象，不是新增图册假设 |
| `PlaneCurveNoetherian` / `PlaneFiniteEtaleTheta` | 标准坐标环 Noetherian；从真实有限 étale 秩二覆盖构造 theta，并在偶性假设下证明截面消失 | 无图册、cocycle 或平方输入；原题指定覆盖及实几何仍未接通 |
| `KummerScalarEquiv` / `SchemePushforwardSourceIso` / `SchemePushforwardIsoChart` | Kummer 系数环同构运输及实际概形箭头同构下的乘法图运输 | 保留实际系数、二次参数与所有限制映射 |
| `SchemePushforwardOpenChart` / `SchemePushforwardKummerCover` | 实际限制态射的乘法图搬回原底并组装全局覆盖，内部构造跨图交叠 | 输入局部图的通用组装；几何接口在下一模块消去图输入 |
| `SchemeFiniteEtaleKummerAtlas` | 从明确几何与秩条件构造原态射在原底上的覆盖乘法图及实际模层图册 | 显式保留 Flat、Noetherian、2 可逆与秩二；未实例化指定判别双覆盖 |
| `SchemeTwoInvertible` / `SchemeFiniteEtaleTrace` | 由覆盖推导任意开集的 2 可逆；唯一层迹、真实核层、秩一标架及符合原环乘法的局部完美平方配对 | 无图册、迹或配对输入；不把任意非仿射开集的截面代数迹当作层迹 |
| `SchemePushforwardRestriction` / `SchemePushforwardAtlasRestriction` | 实际推前结构模层与开限制的典范同构；组合开子概形图册运输 | 适用于任意概形态射；运输接口仍接收限制态射的图册 |
| `KummerModuleTransport` | 模层同构运输、开子概形图册下降、像覆盖及 Sigma 细化覆盖 | 普通模层同构本身不保证保留独立给定的乘法 |
| `SchemePushforwardKummerAtlas` / `SchemePushforwardTrace` | 真实截面环的乘法图自动给出代数交叠；全局迹与覆盖图册选择无关 | 图来自同一实际态射；未假设任意态射均有这些图 |
| `SchemeAffinePresentation` | 实际限制态射与截面环 Spec 态射的同构；从几何条件提取代数性质并构造仿射图册 | 明确保留平坦、Noetherian、2 可逆及秩二；原底上的乘法坐标运输现由后续模块接通 |
| `AffinePushforwardTensor` / `AffinePushforwardPrincipal` / `AffinePushforwardComparison` / `PrincipalOpenTensorGluing` | 真实张量到推前截面的环映射；主开及 Kummer 图内任意子开的自然环同构 | 非仿射子开的证明使用实际两坐标粘合，无额外截面同构输入 |
| `AffinePushforwardModule` / `AffinePushforwardKummerModel` / `AffinePushforwardKummerAtlas` | 实际模层推前、标量相容的真实截面坐标、兼容图册及覆盖存在性 | 仿射态射上的定理；指定双覆盖和非仿射底的运输仍待接通 |
| `KummerBaseChange` / `KummerScalarMap` / `KummerModelRestriction` | 实际基变换同构、坐标与迹的限制公式、限制的恒等及复合律 | 适用于实际基变换代数；不等同于推前层截面识别 |
| `KummerModelOverlap` | 从同一代数的模型构造交叠同构和单位，证明 cocycle、平方及基变换公式 | 共同代数是实际输入，交叠同构与单位在内部构造 |
| `PrincipalOpenSectionMap` / `PrincipalOpenKummerSections` | 任意子开上的真实结构层标量映射及相容的张量代数坐标 | 与实际推前层截面的比较已由后续模块证明 |
| `RankTwoUnimodularBasis` / `PrincipalOpenKummer` | 任意底环上调整秩二基；从素点秩二条件构造主开覆盖及实际局部化代数模型 | 输入模有限表示、平坦、形式非分歧和 2 可逆；实际仿射图册现由后续模块构造 |
| `RankTwoUnitBasis` / `LocalRankTwoKummer` | 从局部环上的有限平坦秩二条件构造基、单位 Kummer 模型及真实迹核平方 | 不输入任何基；指定双覆盖图册仍待证明 |
| `QuadraticNormalForm` / `KummerUnramified` | 实际配方代数同构；从形式非分歧性证明参数可逆 | 使用实际导子与 Kähler 微分模；不假设判别式可逆 |
| `QuadraticBasisModel` / `QuadraticBasisTraceZero` | 从实际基 `(1,e)` 构造单位 Kummer 模型，以及原代数实际迹核的乘法张量平方同构 | 指定双覆盖的相容局部基仍是缺口 |
| `ModuleSheafKernelSections` / `KummerModuleAtlas` | 实际层核的截面识别；从相容局部代数图册粘合全局迹并取真正的核层 | 实际模层与图册仍由调用者提供 |
| `KummerTraceZeroFrames` / `KummerTraceZeroDescent` | 构造核层标架、cocycle、下降同构及平方配对；证明配对等于局部代数乘法 | 一般概形要求各截面环中 2 可逆；平面曲线接口从基域推出 |
| `PlaneThetaTraceZero` | 核层超平面扭曲的 tensor 普遍性质、余切平方同构及条件性截面消失 | 指定判别双覆盖的图册、theta 对应及偶性来源仍待证明 |
| `QuadraticTraceZero` / `QuadraticTraceZeroTransition` | 真实代数迹的核、乘法张量平方同构、实际代数同构诱导的迹零过渡单位及复合关系 | 要求局部模型已给定，识别迹零模要求 2 可逆 |
| `LineBundleSquareTrivialization` / `PlaneThetaKummer` | 从局部实际代数乘法推导系数相容性，粘合 η²≅O，接入 theta 截面消失 | 局部模型与指定全局双覆盖的对应仍需证明 |
| `LineBundleUnitProduct` / `LineBundleRefinement` | 实际平凡因子的乘积消去、任意覆盖细化同构及坐标相容性 | 无需在较大坐标开集上假设 η 平凡 |
| `LineBundleTwoTorsion` / `PlaneThetaTwoTorsion` | 构造 η⊗H、原始因子的 tensor 普遍性质、实际微分层平方同构及条件性截面消失 | η²≅O 和扭曲偶性仍是输入 |
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
| `PlaneThetaLineBundle`、`PlaneThetaSmooth` | 对给定实际局部平凡 theta 层及平方同构证明偶维截面消失；正规性、细化、标架、配对及其完美性均内部构造 | 伴随同构现由后续模块提供；仍需原双覆盖的 theta 数据及后续实几何桥梁 |
| `ChartHomogenization`、`PlaneChartPolynomialMap` | 构造齐次化，证明实际图册多项式映射满射，完整核恰为 `(F,Xᵢ−1)`，并识别原结构态射的基域标量 | 核包含非齐次关系；不以函数域模型替代实际图册 |
| `JacobianLocalization`、`PlaneJacobianPresentation`、`PlaneGradientCover`、`PlaneJacobianSmooth` | 构造有限表示，计算偏导 Jacobian，反演偏导后得到标准光滑图册，再由实际主开覆盖证明结构态射光滑 | Euler 步骤不除以次数，适用于特征 5 |
| `HomogeneousFactors`、`PlaneOriginHeight`、`HomogeneousCommonZero` | 最高齐次分量乘法、原点素理想高度至少 3；由 Nullstellensatz 与 Krull 高度定理证明两个正次齐次三元式有非零公共零点 | 明确使用代数闭域 |
| `ProjectiveJacobianPoints`、`ProjectiveJacobianCriterion`、`JacobianIrreducible` | 构造非零向量对应的实际射影点；证明两种梯度条件等价，并推出方程不可约及主理想素性 | 条件检查原始方程，不是仅检查约化零集 |
| `PlaneThetaJacobian` | 从显式多项式 Jacobian 条件接通 theta 截面消失定理，内部推出素性与实际光滑性 | 伴随同构现由后续模块提供；theta 的几何来源及原实问题仍待完成 |
| `SchemeKaehlerSheaf` | 对实际 `X → Spec K` 构造微分预层、层化和普适导子，证明目标模层上的导子与层态射一一对应 | 不把任意开集上的微分层截面等同于该截面环的微分模 |
| `LocalizedModuleStalk`、`AffineKaehlerPresheafLocalization` | 从真实主开集局部化证明真实茎局部化；将其应用于实际微分预层 | 泛用转移引理的局部化输入在仿射微分情形得到证明 |
| `AffineKaehlerDerivation`、`AffineKaehlerComparison` | 通过实际局部分式导子构造到关联模层的规范比较，并通过真实茎与局部双射证明该比较是同构，且保持实际正则函数的微分 | 本轮通过实际开浸入搬运和限制同构接到曲线的真实层标架 |
| `PlaneKaehlerFrames`、`PlaneCurveKaehlerFrames` | 计算偏导主开集上的实际微分模基，并识别唯一基向量为剩余坐标比的微分；显式对齐实际基域作用 | 该模基现已由后续实际仿射比较搬运成微分层的局部同构 |
| `PlaneDifferentialIdentities`、`PlaneResidueTransition`、`PlaneResidueCrossTransition` | 实际普适导子的链式法则、曲线微分关系、同图册留数换元，以及两类跨图册坐标缩放下的二次留数恒等式 | 已由后续实际留数层模块实例化、统一符号并粘合 |
| `CommRingKaehlerIso`、`TopologyOpenRestriction`、`ModuleSheafificationRestriction` | 环同构诱导真实微分模同构；证明开集像函子的余连续性及模层化与限制相容 | 用真实局部双射与层化单位证明，不预设待证同构 |
| `SchemeModuleRestriction`、`SchemeKaehlerRestriction`、`SchemeKaehlerIsoTransport` | 实际开子概形限制和开浸入下的微分层搬运同构，保持真实导子 | 不把开子概形模层范畴与原站点 `Over U` 定义为相同对象 |
| `TildeModuleFrames`、`AffineKaehlerFrames`、`AffineOpenKaehlerComparison` | 实际单元素基产生关联层和微分层的真正平凡化，并保持坐标微分 | 最终曲线应用内部提供基 |
| `SchemeOpenModuleFrames`、`SchemeOpenDifferentialFrames`、`PlaneCurveDifferentialSheafFrames`、`PlaneCurveDifferentialCover` | 将实际开子概形平凡化转成原曲线所有子开集上的相容标架；从 Jacobian 条件得到每点的实际局部单位层同构 | 生成元、限制与开集等式搬运均已证明 |
| `PlaneCurveResidueIdentities`、`PlaneCurveSheafResidueIdentities`、`PlaneCurveSignedResidueTransitions` | 真实交叠环及真正微分层中的完整留数过渡公式，含两类混合情形与排列符号 | 过渡系数就是已构造超平面 cocycle 的平方 |
| `ModuleFrameRescaling`、`PlaneCurveResidueFrames`、`FrameTransitionComparison`、`PlaneCurveAdjunction` | 构造实际有符号留数标架，比较全部过渡并粘合得到 `Ω¹(C/K) ≅ PlaneCurveQuadraticSheaf F` | 原双覆盖的 theta 来源仍是独立问题 |
| `PlaneThetaAdjunction` | 实际平方同构 `Θ² ≅ Ω¹(C/K)` 加偶性推出每个 theta 截面为零，伴随同构内部提供 | 仍需指定 theta 的实际局部平凡化、平方同构及偶性 |
| `CofactorCover` | 带显式 twist 参数的余子式根属于矩阵核；特征不为二时，含非零根的根集合恰有两点；在显式小行列式关系下构造根 | 判别式符号的几何识别；从余秩推出小行列式关系；覆盖的下降、étale 性与 theta 对应 |
| `IsotropicDimension` | 维数和超过环境维数的子空间有非零交；显式分裂二次型的五维子空间限制各向同性 | 从 Clifford 指数和序得到 Pfister 邻形式并证明分裂 |
| `Incidence` | 非零 `2×2` 小行列式条件下，两条齐次线性方程有唯一规范化解，并给出集合等价 | 非空稠密开集、正则映射、概形同构及实双有理性 |
| `ConnectedComponents` | 实际拓扑连通分支商 `ConnectedComponents X` 在 `ConnectedSpace X` 假设下基数为一 | 为所研究的实代数簇证明该连通性假设 |

特别地，`ConnectedComponents` 中的连通性是**显式假设**；这个模块没有从圆锥曲线丛的几何条件推出连通性。

## 当前接通的证明链

一般 theta 接口的定理是 `planeQuintic_even_theta_sections_eq_zero_of_cotangent_square`。输入精确为：

- 代数闭基域、齐次五次式 `F`，且 `totalDegree F = 5`。
- 原始方程的 Jacobian 条件：对每个非零向量 `v : Fin 3 → K`，若 `F(v)=0`，则至少一个偏导 `∂ᵢF(v)≠0`。
- 实际模层 `Θ`、一个开覆盖 `Uᵢ`，以及每个 `Uᵢ` 上到单位层的实际同构。覆盖成员无须预先仿射或非空。
- 由这些平凡化构造的平方 cocycle 层到真实 `schemeKaehlerSheaf (planeCurveStructure F)` 的实际同构。伴随同构到 `PlaneCurveQuadraticSheaf F` 在定理内部提供。代码证明该平方层表示 `Θ×Θ` 到任意模层的自然双线性配对。
- 偶性 `Even (finrank K Γ(Θ))`。

方程的素性、实际曲线的整性、光滑性与正规性、实际 `H,T`、三个截面、共同仿射细化、theta 标架与完美配对、实际二次满射及精确四次单射都已由代码提供。**没有假设任意 theta 在三个完整坐标开上平凡**。有限维性和 `h⁰(H)=3` 也在证明内部推出。较低层的素性、光滑态射及正规标架接口仍保留。最终定理调用一般实际模层定理 `even_theta_ineffective_of_restriction_maps`，其截面论证如下。

证明先由满射性提升 `s²,st,t²`，用实际配对推导共同权重，再从 `AD=B²` 得到

$$
A=ca^2,\qquad B=cab,\qquad D=cb^2,\qquad c\ne0.
$$

这给出一个真实非零 `H` 截面及真实全局平方恒等式。局部完美配对提供单位系数，整闭性把平方商延拓成单位，实际局部比较态射再粘合成 `Θ≅H`。同一组限制条件还强制三个坐标截面构成 `H` 截面空间的基；二次满射与非零截面的配对注入则证明 `Θ` 截面有限维。于是两个独立截面会迫使 `h⁰(Θ)=3`，与正偶数维数矛盾。局部权重、交叠相容性、维数和最终同构均在证明中构造。

**几何实例化已有推进，但仍是条件结论。** `PlaneCurveScheme` 构造的是实际 `Proj K[X₀,X₁,X₂]` 内 `V(F)` 的约化诱导闭子概形。素性、齐次性和次数条件给出实际整性、泛点描述及三个非空仿射开覆盖。`LineBundleSheaf` 从 `Xⱼ/Xᵢ` 的单位过渡数据构造真正模层，`PlaneHyperplaneSheaf` 构造其三个真正全局截面；这些截面的泛点系数已与实际射影坐标相连。四次单射通过实际概形态射及泛点素理想证明，常数与结构态射的基域作用也已识别；`planeQuintic_hyperplane_quartic_injective` 给出三个实际全局截面所需的精确 `aeval` 单射形式。

**实际二次截面映射满射的缺口现已补上。** 证明先从实际闭浸入和射影图册同构提升局部正则函数，再在任意一次式图册上粘合 `s/L²`，得到次数精确的齐次分子。完整齐次限制核把分子的泛点相容性变成原锥商环中的等式；实际多项式坐标变换与首一有限自由商环提供两条适当一次式的清分母性质，齐次投影最后提取二次式。实际全局截面的泛点单射证明该二次式确实限制为原截面。首一性与坐标选择都在证明内部取得。

这里没有把整个锥分式域等同于曲线函数域：保留次数的锥嵌入以 `k(C)[T]` 为目标。图册的完整商环表示现在已证明，但尚未构造与 `Proj(K[X₀,X₁,X₂]/(F))` 的显式全局同构。实际相对微分层与已构造超平面平方层的伴随同构现已证明。仍须从原实圆锥曲线丛及其判别双覆盖构造方程、复化数据、指定 theta 模层、局部平凡化及其平方到相对微分层的同构。


**原始方程与约化零集必须区分。** `F=X₀^5` 的约化射影零集是光滑直线，但 `(F)` 并非素理想；因此仅凭约化曲线光滑不能删去原方程的素性假设。新定理使用实际偏导值的 Jacobian 条件，该条件排除了这一退化。不可约性证明先用零点定理与高度定理证明两个正次齐次因子必有非零公共零点，再在该点用乘积求导得到所有偏导为零的矛盾。

实际光滑性证明将每个图册表示为三个生成元、两个关系 `(F,Xᵢ−1)` 的商环。选择 `j≠i`，对应 Jacobian 为 `∂ⱼF`；反演其实际截面得到标准光滑的相对维数一代数。Euler 恒等式保证这些偏导主开集覆盖曲线。所有表示、局部化、覆盖与结构态射的标量比较均由代码证明。

[theta 引理的纸面证明与精确形式化边界](docs/THETA_BRIDGE_REVIEW.md) 保留完整数学论证。形式化采取局部单位与实际层同构路线；纸面证明中的除以二只发生在实际除子群中，不能在 Picard 群中这样消去。

[实几何与二次型论证的审查](docs/REAL_OBSTRUCTION_AUDIT.md) 另行核查实双覆盖的 twist、Brauer 类、Albert/Pfister 论证和有理性路线。这是有精确文献依据的非形式化论证，不是 Lean 证书。

余子式方程现在写作 `vᵢvⱼ=twist*adj(M)ᵢⱼ`。正、负两种选择都被支持；代码没有把三阶矩阵的负号约定自动移用于目标五阶矩阵。

## 构建与审计

本版包含 241 个源码模块、1556 条公开手写定理，另有 15 条私有辅助定理（共 1571 条手写定理）。本地整体构建及公理审计均已通过；完整计数和记录见 `verification/summary.json`。审计包含 Lean 自动生成的声明，不能与手写定理数混同。

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
