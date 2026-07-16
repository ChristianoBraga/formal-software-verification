# Formal Software Verification — Lecture Notes

Lecture notes for the course *Verificação Formal de Software* (IME, Mestrado em
Sistemas e Computação), written in [Verso](https://github.com/leanprover/verso).

**Published site:** <https://christianobraga.github.io/formal-software-verification/>
([English](https://christianobraga.github.io/formal-software-verification/en/) ·
[Português](https://christianobraga.github.io/formal-software-verification/pt/)).
Every push to `main` rebuilds and redeploys the site via GitHub Actions
(`.github/workflows/deploy.yml`); the landing page lives in `site/`.
The notes exist in two languages, with parallel document trees:

- `Lectures/En/` — English lectures, root document `Lectures/En.lean`
- `Lectures/Pt/` — Portuguese lectures, root document `Lectures/Pt.lean`

Lean code is identical in both versions; only the prose differs.

## Building

```
lake exe lectures-en --output _out/en
lake exe lectures-pt --output _out/pt
```

Each build writes a multi-page HTML site to its output directory. The exercise
files extracted from `savedLean` blocks (one file per lecture module) land in
`html-multi/example-code/`, inside the served site, and each lecture's
Exercises section links to its file.

## Viewing

Verso's HTML must be served, not opened directly from the filesystem:

```
python3 -m http.server 8000 --directory _out/en/html-multi
```

## Adding a lecture

1. Create `Lectures/En/LectureNN.lean` and `Lectures/Pt/LectureNN.lean`
   (start from Lecture01 as a model).
2. Import and `{include 0 ...}` them in `Lectures/En.lean` and `Lectures/Pt.lean`.
3. Put exercises in `savedLean` blocks so they are extracted for students.
4. Add formal citations to `Lectures/Papers.lean` when Verso's citation types
   fit (`InProceedings`, `Article`, `Thesis`, `ArXiv`); otherwise use margin
   notes with the full reference.
