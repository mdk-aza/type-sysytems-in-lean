# Lean 4 による型システム形式化プロジェクト

![Lean](https://img.shields.io/badge/Lean-4-blue)
![Status](https://img.shields.io/badge/status-in_progress-yellow)
![License](https://img.shields.io/badge/license-MIT-green)

🇺🇸 English version → [README.md](README.md)

---

このリポジトリは、Lean 4 を用いて**型システム・操作的意味論・プログラミング言語理論**を形式化する、研究志向のプロジェクトです。

本プロジェクトは以下の書籍に着想を得ています：

> Benjamin C. Pierce, *Types and Programming Languages (TaPL)*

そして、そこから発展して以下のような高度なトピックへ拡張していくことを目的としています：

- 双方向型付け（Bidirectional Typing）
- 部分型（Subtyping）
- 多相型（System F）
- 依存型
- 効果システム

---

## 🎯 目的

本プロジェクトの目的は以下の通りです：

- **形式化（Formalization）**  
  プログラミング言語理論のコア概念を Lean 4 で実装する

- **再構成による理解**  
  定義や証明を一から再構築することで理解を深める

- **検証（Verification）**  
  以下のような性質を証明する：
    - preservation（保存性）
    - progress（進行）
    - determinism（決定性）
    - soundness（健全性）

- **研究基盤の構築**  
  型システム・形式手法・メタ理論研究のための再利用可能な基盤を作る

---

## 📚 スコープ

本リポジトリは、複数の形式化プロジェクトから構成されています。

### 主な対象

- 数学的基礎（関係・順序・閉包）
- 非型付き算術式
- 操作的意味論
- 単純型付きラムダ計算（STLC）
- 双方向型付け
- 部分型
- System F
- 依存型

---

## 🏗️ ディレクトリ構成

    TypeSystemsInLean/
    ├── Common/          # 共通基盤（関係・補題など）
    ├── TaPL/            # TaPLベースの形式化
    ├── Bidirectional/   # 双方向型付け
    ├── Subtyping/       # 拡張予定
    ├── SystemF/         # 拡張予定
    └── lakefile.lean

---

## 🧠 設計方針

- **再構成重視**  
  単なる翻訳ではなく、Lean向けに理論を再設計する

- **レイヤー構造**  
  共通基盤の上に各型システムを構築する

- **拡張性**  
  将来の研究に耐えうる構造を意識する

- **研究志向**  
  学習用途に留まらず、研究基盤として利用する

---

## ⚙️ セットアップ

以下を実行してください：

    lake update && lake exe cache get
    lake build

---

## 📄 ライセンス

MIT License
