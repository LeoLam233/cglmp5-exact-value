# CGLMP5 — AI-assisted candidate research artifact v0.1

候选 **C001**。这是标准五结果 CGLMP 精确量子最大值的 AI 辅助计算机证明候选，以及本次后验核验的冻结材料。原生成运行的 SUCCESS 经过 PROVISIONAL_SUCCESS 入场处理；本次最终生命周期、门槛及证据类别以 [verification/CANDIDATE.json](verification/CANDIDATE.json) 和 [verification/RECORD.md](verification/RECORD.md) 为准。

采用局域隐变量界2的归一化，候选定理为：任意局部 Hilbert 维数、任意局部五结果 POVM 下，`sup I5 = mu`；mu 是

`5 mu^6 - 65 mu^4 + 144 mu^2 + 96 mu + 16 = 0`

的最大实根，`mu = 3.015710475522673285523983801961043281714038985152…`。五维双体策略取到等号。普适上界来自14项正权的精确非交换 SOS，系数是整数/代数编码，未依赖数值优化容差。先读 [PROOF.md](PROOF.md) 和 [ROOT_EMBEDDING.md](ROOT_EMBEDDING.md)；有限表 [SOS14.json](SOS14.json) 是证明对象的一部分。

新增贡献主张是完整精确证书及范围桥接。小数、Fourier 测量及候选态有既有来源。本次有限检索没有找到实质先例冲突；不主张绝对首次。仅解决五结果情形，不主张所有结果数、测量唯一性或自检。

## 复现

在本包的**工作副本**中运行。四个核心入口只需 Python 标准库，实际新增测试环境为 Windows 11 / CPython 3.12.14。提交的 Linux / Python 3.13.5 回执属于原运行历史，不是本次新执行。

```sh
python -B validate_integer_encoding.py --output encoding_current.json
python -B verify_sos14.py --output sos_current.json
python -B verify_independent.py --output gram_current.json
python -B verify_statement.py --output statement_current.json
python -B kill_tests.py
```

要求退出码0及 `PASS` / `ALL_TESTS_PASSED`。最后一个入口会写 `KILL_TESTS.json`，所以始终使用工作副本；生成结果不属于冻结清单。程序重新计算恒等式和区间，不把 JSON 历史 PASS 标签当数学前提。

`MANIFEST.sha256` 覆盖本包所有常规文件，排除清单自身；解压后的新输出不在覆盖范围。外层 ZIP 的哈希及解压后复跑实测回执在包外 sidecar，避免自引用。

新增严格preflight处理审计发现ALG-01：原int()解析会把非法0.5系数读作0。原1524标量均符合整数格式，协调者确认这不损害C001，补充入口会拒绝该非法副本。原核验器和证书保持字节，首报和缺陷复现未被删除。

额外审计重放需要在工作副本运行；代数精确重放只需标准库，物理和下界脚本还需NumPy。这些程序会写报告到各自副本目录：

```sh
python -B verification/receipts/audit_algebra/audit_exact.py --input-dir verification/receipts/input_views/audit_view
python -B verification/receipts/audit_physics/audit_exact.py verification/receipts/input_views/audit_view
python -B verification/receipts/reconstruction/lower_worker/reconstruct.py
```

## 本次证据及界限

本次为分离上下文子代理 AI 敌对审计、受限输入重建、精确程序复跑与解析接口核查。首轮审计隐藏了历史通过摘要及其他审计结论；共享文件系统仍存在，不宣称操作系统层隔离、不同模型训练来源或外部人类独立性。

各证据的实际输入、程序、覆盖和局限见 [核验记录](verification/RECORD.md)；原始首轮报告与计算回执在 [receipts](verification/receipts)。没有完整全定理无提示重建、Lean 形式化、人类同行评议或外部专家确认。冻结状态表示本工作流的科学材料 readiness；数学评估为 `NOT_REFUTED_BY_RECORDED_CHECKS`，不是不可出错的正确性认证。

PROOF.md §7–8 与提交脚本头部的“同一代理实现”“未做外部审计”描述原生成运行，原字节为可比对目的保留。**本次**新审计及新实现由本次 receipt 明确追加，不能把旧说明误当本次证据缺失，也不能把本次 AI 子代理说成人类同行评议。引用4的作者名元数据应读为 Ming-Guang Hu；原件书目拼写保留并在核验记录中更正。

完整输入史无法恢复：较早工作区曾丢失，完整生成对话与早期笔记未供应。现有精确数据及每个最终推论被当作不可信对象检查，未把缺失推理作为证明权威；历史发现影响仍披露。两份供应 ZIP 和私人原回执保留在本地输入档案，本包只保留其哈希、身份及相关来源比较，未打包第三方论文全文或私人对话。

本地归档未发布到 GitHub、Zenodo 或 arXiv，没有本项目的已核验公开优先权时间戳。作者、ORCID、许可证未被指定，因此未擅自添加作者/开源授权。
