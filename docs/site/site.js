"use strict";

const root = document.body.dataset.root;
const input = document.querySelector("#library-search");
const contents = document.querySelector(".contents");
const compactLayout = window.matchMedia("(max-width: 880px)");

function setContentsLayout() {
  contents.open = !compactLayout.matches;
}

setContentsLayout();
compactLayout.addEventListener("change", setContentsLayout);

function typesetMath(element) {
  if (!window.katex) return;
  for (const formula of element.querySelectorAll("[data-tex]")) {
    window.katex.render(formula.dataset.tex, formula, {
      displayMode: formula.dataset.display === "true",
      throwOnError: false,
      trust: false,
    });
  }
}

document.addEventListener("DOMContentLoaded", () => {
  typesetMath(document.querySelector(".layout"));
});

if (document.body.dataset.home === "true" && /^#COL-[0-9]{4,}$/.test(location.hash)) {
  location.replace(root + "tag/" + location.hash.slice(1) + "/");
}

document.addEventListener("keydown", (event) => {
  if (event.key === "/" && !["INPUT", "TEXTAREA"].includes(document.activeElement.tagName)) {
    event.preventDefault();
    input.focus();
  }
});
for (const button of document.querySelectorAll("button[data-copy]")) {
  button.addEventListener("click", async () => {
    try {
      await navigator.clipboard.writeText(button.dataset.copy);
      button.textContent = "Copied";
    } catch {
      const range = document.createRange();
      range.selectNodeContents(button.parentElement.querySelector("code"));
      const selection = window.getSelection();
      selection.removeAllRanges();
      selection.addRange(range);
      button.textContent = "Selected";
    }
    setTimeout(() => { button.textContent = "Copy"; }, 1400);
  });
}

const results = document.querySelector("#search-results");
if (results) {
  const status = document.querySelector("#search-status");
  input.value = new URLSearchParams(location.search).get("q") || "";
  let index = [];
  function render() {
    const query = input.value.trim().toLocaleLowerCase();
    const matches = query ? index.filter((item) => item.terms.includes(query)) : [];
    results.replaceChildren();
    status.textContent = query
      ? matches.length + (matches.length === 1 ? " match" : " matches")
      : "Enter a permanent ID, result, Lean declaration, module, author or source locator.";
    for (const item of matches) {
      const article = document.createElement("article");
      article.className = "search-result";
      const label = document.createElement("p");
      label.className = "item-label";
      label.textContent = (item.id ? item.id + " · " : "") + item.kind + " · " + item.section;
      const title = document.createElement("h2");
      const link = document.createElement("a");
      link.href = root + item.path;
      // Only the generated prose fields carry escaped HTML fragments.
      if (item.title_html !== undefined) link.innerHTML = item.title_html;
      else link.textContent = item.title;
      title.append(link);
      const statement = document.createElement("p");
      if (item.kind === "declaration") {
        const code = document.createElement("code");
        code.textContent = item.statement;
        statement.append(code);
      } else if (item.statement_html !== undefined) {
        statement.innerHTML = item.statement_html;
      } else {
        statement.textContent = item.statement;
      }
      article.append(label, title, statement);
      results.append(article);
    }
    typesetMath(results);
  }
  document.querySelector("form.search").addEventListener("submit", (event) => {
    event.preventDefault();
    history.replaceState(null, "", "?q=" + encodeURIComponent(input.value));
    render();
  });
  input.addEventListener("input", render);
  fetch(root + "search.json").then((response) => {
    if (!response.ok) throw new Error("The search index could not be loaded.");
    return response.json();
  }).then((data) => {
    index = data;
    render();
  }).catch((error) => { status.textContent = error.message; });
}
