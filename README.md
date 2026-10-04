# EvenQuinticConic

**部分形式化项目；尚未证明原几何问题的存在性或不存在性。**

本项目尝试核查如下问题的一份候选“不存在性”论证：是否存在光滑射影、几何标准的实圆锥曲线丛
`X → ℙ²_ℝ`，其判别曲线为光滑五次曲线，判别双覆盖对应偶 theta characteristic，且实点集有两个连通分支？

当前已接通一个关于**实际概形与实际模层的条件定理**：在明确的限制映射、局部标架及局部配对假设下，两个独立截面迫使 `Θ≅H`；代码还内部推出 `h⁰(H)=3` 和 `Θ` 截面空间有限维，因此偶维数推出每个 `Θ` 截面均为零。这些结论通过真实结构态射、配对、单位延拓和层态射粘合证明。代码尚未把这些输入全部从指定光滑平面五次曲线推导出来，也没有形式化原问题的实几何与连通性结论。因此，**编译成功不表示原存在性问题已解决，也不验证此前整个非形式化证明**。

## 已形式化的内容

| 模块 | 实际数学内容 | 仍未覆盖的应用步骤 |
| --- | --- | --- |
| `PolynomialDegree` | 非零五次多项式整除次数至多四的 `A*D-B²` 时，该式为零；也给出主理想版本 | 从曲线上的截面关系得到主理想成员关系；theta 的分类 |
| `RankOneFactorization` | 在 GCD 幺半群中由 `AD=B²` 推出 `A=ha², B=hab, D=hb²`，包括退化情形 | 将多项式因子转成线丛信息 |
| `ConicClassification` | 不成比例的二次式迫使 `h` 是非零常数、`a,b` 的次数至多一 | 从独立截面得到所需多项式假设 |
| `HomogeneousConics` | 将齐次二次式分解为共同非零常数乘齐次一次式的平方/乘积；接上五次式主理想关系 | 从指定曲线提供实际限制映射条件 |
| `IndependentSquares` | 在代数闭域上的整代数中，线性无关的两个元素的平方仍线性无关 | 为实际线丛截面构造兼容乘法的整代数模型与限制映射 |
| `RestrictionModel` | 从实际代数同态、核等于五次式主理想及独立元素的平方/乘积像，推导完整齐次因子分解 | 为几何线丛截面构造满足这些条件的模型 |
| `GradedRestriction` | 实际构造 `Xᵢ ↦ fᵢT`，逐次刻画核；从齐次消失条件识别主理想，证明注入系数扩张保持核 | 为实际曲线证明齐次消失条件 |
| `WeightedRestriction` | 保留公共非零权重 `u`，由三个加权乘积等式推出齐次分解，无须假设 `u` 是平方 | 为指定曲线构造实际乘法配对 |
| `SquareExtension` | 在实际代数闭包中构造平方根及保持原底域线性无关性的多项式模型 | 几何泛点截面的构造；加权路线无需使用此扩域 |
| `FiniteDegreeRestriction` | 仅假设四次齐次式的限制单射，即得到同一个二次式分解，无需完整主理想核 | 曲线上实际限制映射的单射性及二次式提升 |
| `GenericCoefficientModel` | 从实际系数、加权乘积与限制条件，得到分解及 `u*(α/a(f))²=c≠0`；支持完整核或仅四次单射两种接口 | 将指定曲线接入已证明的实际模层比较定理 |
| `LocalSquareUnit` | 整闭环的分式域中，正次幂为环内单位的元素来自环内单位；包括加权与商的版本 | 为指定几何线丛构造局部系数恒等式 |
| `GenericPointInjection` | 实际整概形的泛点相等判据、限制相容性，以及整闭仿射开集上的唯一单位延拓 | 从目标光滑曲线提供这些整闭仿射开集 |
| `SheafGluing` | 使用真实层公理粘合截面；同一有理函数的局部单位唯一粘合；局部正次幂为单位推出全局单位 | 为 theta 比值提供相应几何局部数据 |
| `SheafTrivialization` | 构造真实模层态射 `r↦r•s`，由局部单位坐标构造真实模层同构 | 构造目标线丛与它的局部标架 |
| `LocalFrames` | 定义与实际限制映射相容的局部标架；从兼容局部单位截面构造全局生成元及 `O≅M` | 指定 theta 线丛的标架及有理截面 |
| `RationalSectionFrames` | 在实际整概形的整闭仿射覆盖上，从遵守真实过渡关系、正次幂为局部单位的有理系数，构造全局生成元及实际 `O≅M` | 为 `theta⊗O(-1)` 构造这些局部系数和恒等式 |
| `ModuleGenericInjection` | 实际带局部标架的模层全局截面由任一非空标架开集上的泛点系数唯一确定 | 将该接口应用于目标 theta 线丛 |
| `SchemeScalarAction` | 从实际结构态射 `X→Spec K` 构造基域作用、scalar towers 和 `K`-线性泛点映射，保持独立性 | 指定曲线及线丛的实例化 |
| `RankOnePairing` | 实际秩一模的双线性配对等于标架系数乘坐标乘积；实际 tensor map 双射推出该系数是单位 | 提供几何的局部完美配对 |
| `ModulePairing` | 自然双线性配对给出真实截面乘积和共同泛点权重；由全局平方恒等式推导局部单位权重 | 为 theta 平方同构构造实际配对 |
| `ModuleHomGluing` | 粘合相容的实际局部模层态射；局部双射构造全局实际同构 | 实例化目标曲线的局部数据 |
| `FrameComparison` | 非零真实源截面与局部加权平方关系推出实际 `N≅M`；内部推导比较态射的交叠相容性 | 从几何构造局部平方关系 |
| `PairingComparison` | 全局配对恒等式 `μ(s,s)=cν(a,a)`、`a≠0`、单位 `c` 推出实际同构，并把 `a` 送到 `s` | 目标配对、整闭仿射覆盖 |
| `ThetaSectionBridge` | 用实际泛点系数、齐次分解和配对比较，从二次式提升与四次单射得到实际 `Θ≅H` | 从指定曲线验证限制条件 |
| `QuadraticSections` | 从三个真实 `H` 截面和实际配对构造齐次二次式的线性截面映射；证明泛点公式；满射性给出真实提升 | 证明该具体映射在目标曲线上满射 |
| `GlobalSectionDimension` | 实际模层同构诱导基域线性截面等价及维数相等；维数至少二给出两个独立截面 | 将一般结论应用于指定曲线 |
| `ThetaFiniteDimension` | 实际二次截面映射满射使 `T` 被六个截面生成；非零截面配对给出注入，内部推出 `Θ` 截面有限维 | 为指定曲线证明实际二次满射 |
| `HyperplaneDimension` | 四次单射使三个坐标截面独立，二次满射使其张成；构造真实基并推出 `h⁰(H)=3` | 为指定曲线验证两项限制条件 |
| `ThetaIneffectivity` | 从实际限制条件和局部层数据推出 `h⁰(Θ)≥2⇒Θ≅H`；内部证明维数结论后，偶性推出每个截面为零 | 从光滑平面五次曲线验证全部几何输入 |
| `PlaneQuintic` | 实际齐次主理想、射影消失集和锥商环；在锥分式域及归一化坐标中证明五次以下齐次限制单射，特别是四次单射 | 将锥/坐标模型接到曲线的实际 `Spec`/`Proj` 概形、twist 层及泛点坐标 |
| `CofactorCover` | 带显式 twist 参数的余子式根属于矩阵核；特征不为二时，含非零根的根集合恰有两点；在显式小行列式关系下构造根 | 判别式符号的几何识别；从余秩推出小行列式关系；覆盖的下降、étale 性与 theta 对应 |
| `IsotropicDimension` | 维数和超过环境维数的子空间有非零交；显式分裂二次型的五维子空间限制各向同性 | 从 Clifford 指数和序得到 Pfister 邻形式并证明分裂 |
| `Incidence` | 非零 `2×2` 小行列式条件下，两条齐次线性方程有唯一规范化解，并给出集合等价 | 非空稠密开集、正则映射、概形同构及实双有理性 |
| `ConnectedComponents` | 实际拓扑连通分支商 `ConnectedComponents X` 在 `ConnectedSpace X` 假设下基数为一 | 为所研究的实代数簇证明该连通性假设 |

特别地，`ConnectedComponents` 中的连通性是**显式假设**；这个模块没有从圆锥曲线丛的几何条件推出连通性。

## 当前接通的证明链

`even_theta_ineffective_of_restriction_maps` 的对象是实际整 `K`-概形上的实际模层 `Θ,H,T`，不是用命题名称替代几何对象。其主要输入仍明确列在定理中：

- 代数闭基域及实际结构态射 `X→Spec K`；整闭坐标环的非空仿射覆盖，以及三层在这些开集上与限制映射相容的秩一标架。
- 实际自然配对 `μ:Θ×Θ→T`、`ν:H×H→T`，在覆盖开集上的实际 tensor map 均双射。
- 三个真实 `H` 截面生成的 `quadraticSectionMap` 满射，以及这些截面泛点坐标上的四次齐次限制单射。
- 偶性 `Even (finrank K Γ(Θ))`。有限维性和 `h⁰(H)=3` 都在证明内部推出，不再作为独立输入。

证明先由满射性提升 `s²,st,t²`，用实际配对推导共同权重，再从 `AD=B²` 得到

$$
A=ca^2,\qquad B=cab,\qquad D=cb^2,\qquad c\ne0.
$$

这给出一个真实非零 `H` 截面及真实全局平方恒等式。局部完美配对提供单位系数，整闭性把平方商延拓成单位，实际局部比较态射再粘合成 `Θ≅H`。同一组限制条件还强制三个坐标截面构成 `H` 截面空间的基；二次满射与非零截面的配对注入则证明 `Θ` 截面有限维。于是两个独立截面会迫使 `h⁰(Θ)=3`，与正偶数维数矛盾。局部权重、交叠相容性、维数和最终同构均在证明中构造。

**这些仍是条件结论。** 尚未证明指定光滑平面五次曲线满足全部输入。`PlaneQuintic` 已对实际商环 `K[X₀,X₁,X₂]/(F)` 的分式域和归一化坐标证明四次单射，但没有把该锥分式域直接当作曲线函数域；这些归一化限制结果与实际曲线及 twist 层坐标的对应尚待完成，不能把整个锥分式域与曲线函数域等同。还需为该曲线证明实际二次截面映射的满射性，并提供局部配对与整闭标架覆盖。维数三和有限维性将由这些输入自动推出。

[theta 引理的纸面证明与精确形式化边界](docs/THETA_BRIDGE_REVIEW.md) 保留完整数学论证。形式化采取局部单位与实际层同构路线；纸面证明中的除以二只发生在实际除子群中，不能在 Picard 群中这样消去。

[实几何与二次型论证的审查](docs/REAL_OBSTRUCTION_AUDIT.md) 另行核查实双覆盖的 twist、Brauer 类、Albert/Pfister 论证和有理性路线。这是有精确文献依据的非形式化论证，不是 Lean 证书。

余子式方程现在写作 `vᵢvⱼ=twist*adj(M)ᵢⱼ`。正、负两种选择都被支持；代码没有把三阶矩阵的负号约定自动移用于目标五阶矩阵。

## 构建与审计

本版包含 35 个源码模块、196 条公开手写定理，另有 2 条私有辅助定理。本地构建和公理审计均通过；审计检查的 469 个声明包含 360 个 theorem 声明，其中包括 Lean 自动生成的声明，不能与手写定理数混同。

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
