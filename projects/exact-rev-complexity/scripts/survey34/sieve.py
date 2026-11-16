#!/usr/bin/env python3
"""Merge S2 + OpenAlex citing papers per core paper, fill abstracts, apply the fixed term sieve."""
import json
import os
import re

RAW = os.path.join(os.path.dirname(os.path.abspath(__file__)), "survey34_raw")

# Fixed BEFORE looking at results (2026-09-18). See survey34_s2.md for rationale of the 2 variants.
TERMS = {
    "parallel": r"parallel",
    "depth": r"depth",
    "makespan": r"makespan",
    "simultaneous": r"simultaneous",
    "window": r"window",
    "earliest": r"earliest",
    "slack": r"\bslack",
    "schedule": r"schedul",
    "time-optimal": r"time[- ]optimal",
    "minimum time": r"minim(?:um|al) time",
}
TOPIC = r"pebbl"

CORE = ["Kralovic2004", "Meuli2019", "BHL2022", "BHL2025", "Komarath2016", "Knill1995",
        "LevineSherman1990", "Chan2013", "Bhattacharjee2019", "Bennett1989",
        "ParentRoettelerSvore2015", "LiVitanyi1996"]


def norm(t):
    return re.sub(r"[^a-z0-9]+", "", (t or "").lower())


def load(k):
    s2p = os.path.join(RAW, f"s2_citations_{k}.json")
    oap = os.path.join(RAW, f"openalex_citations_{k}.json")
    s2 = [c["citingPaper"] for c in json.load(open(s2p))] if os.path.exists(s2p) else []
    oa = json.load(open(oap)) if os.path.exists(oap) else None
    return s2, oa


def merge(k):
    s2, oa = load(k)
    rows, by_doi, by_title = [], {}, {}
    for p in s2:
        ext = p.get("externalIds") or {}
        r = {"title": p.get("title"), "year": p.get("year"), "venue": p.get("venue"),
             "doi": (ext.get("DOI") or "").lower() or None, "arxiv": ext.get("ArXiv"),
             "s2id": p.get("paperId"), "oaid": None, "abstract": p.get("abstract"),
             "abs_src": "S2" if p.get("abstract") else None, "in_s2": True, "in_oa": False,
             "authors": [a.get("name") for a in (p.get("authors") or [])][:6]}
        rows.append(r)
        if r["doi"]:
            by_doi[r["doi"]] = r
        by_title.setdefault(norm(r["title"]), r)
    for w in (oa or []):
        doi = (w.get("doi") or "").lower().replace("https://doi.org/", "") or None
        r = by_doi.get(doi) if doi else None
        if r is None:
            r = by_title.get(norm(w.get("title")))
        if r is None:
            r = {"title": w.get("title"), "year": w.get("year"), "venue": w.get("source"), "doi": doi,
                 "arxiv": None, "s2id": None, "oaid": w["id"], "abstract": w.get("abstract"),
                 "abs_src": "OA" if w.get("abstract") else None, "in_s2": False, "in_oa": True, "authors": []}
            rows.append(r)
            if doi:
                by_doi[doi] = r
            by_title.setdefault(norm(r["title"]), r)
        else:
            r["in_oa"] = True
            r["oaid"] = w["id"]
            if not r["abstract"] and w.get("abstract"):
                r["abstract"] = w["abstract"]
                r["abs_src"] = "OA"
    return rows, (oa is not None)


def hits(r):
    text = ((r["title"] or "") + " \n " + (r["abstract"] or "")).lower()
    h = {name: len(re.findall(pat, text)) for name, pat in TERMS.items()}
    h = {k: v for k, v in h.items() if v}
    return h, bool(re.search(TOPIC, text))


if __name__ == "__main__":
    summary, merged_all = {}, {}
    for k in CORE:
        rows, has_oa = merge(k)
        for r in rows:
            r["hits"], r["pebbl"] = hits(r)
        merged_all[k] = rows
        summary[k] = {
            "s2": sum(r["in_s2"] for r in rows),
            "openalex": sum(r["in_oa"] for r in rows) if has_oa else None,
            "both": sum(r["in_s2"] and r["in_oa"] for r in rows) if has_oa else None,
            "s2_only": sum(r["in_s2"] and not r["in_oa"] for r in rows) if has_oa else None,
            "oa_only": sum(r["in_oa"] and not r["in_s2"] for r in rows) if has_oa else None,
            "union": len(rows),
            "with_abstract": sum(bool(r["abstract"]) for r in rows),
            "title_only": sum(not r["abstract"] for r in rows),
            "term_hit": sum(bool(r["hits"]) for r in rows),
            "pebbl_hit": sum(r["pebbl"] for r in rows),
            "term_or_pebbl": sum(bool(r["hits"]) or r["pebbl"] for r in rows),
            "term_and_pebbl": sum(bool(r["hits"]) and r["pebbl"] for r in rows),
        }
    json.dump(merged_all, open(os.path.join(RAW, "merged_citations.json"), "w"), ensure_ascii=False, indent=1)
    json.dump(summary, open(os.path.join(RAW, "sieve_summary.json"), "w"), indent=1)
    cols = ["s2", "openalex", "both", "s2_only", "oa_only", "union", "with_abstract", "title_only",
            "term_hit", "pebbl_hit", "term_or_pebbl", "term_and_pebbl"]
    print("core | " + " | ".join(cols))
    for k, v in summary.items():
        print(k, "|", " | ".join(str(v[c]) for c in cols))
    # global unique
    uniq = {}
    for k, rows in merged_all.items():
        for r in rows:
            key = r["doi"] or norm(r["title"])
            u = uniq.setdefault(key, dict(r, cites=[]))
            u["cites"].append(k)
    print("GLOBAL unique citing papers:", len(uniq),
          "| term_hit:", sum(bool(u["hits"]) for u in uniq.values()),
          "| pebbl:", sum(u["pebbl"] for u in uniq.values()),
          "| term_or_pebbl:", sum(bool(u["hits"]) or u["pebbl"] for u in uniq.values()),
          "| no abstract:", sum(not u["abstract"] for u in uniq.values()))
    json.dump(list(uniq.values()), open(os.path.join(RAW, "merged_unique.json"), "w"), ensure_ascii=False, indent=1)
