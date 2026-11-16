#!/usr/bin/env python3
"""Semantic Scholar Graph API helper. Key comes from env S2_API_KEY only (never logged/written)."""
import json
import os
import sys
import time
import urllib.parse
import urllib.request
import urllib.error

BASE = "https://api.semanticscholar.org/graph/v1"
KEY = os.environ.get("S2_API_KEY", "")
_last = [0.0]


def get(path, params=None, retries=8):
    url = BASE + path
    if params:
        url += "?" + urllib.parse.urlencode(params)
    for attempt in range(retries):
        dt = time.time() - _last[0]
        if dt < 1.2:
            time.sleep(1.2 - dt)
        req = urllib.request.Request(url, headers={"x-api-key": KEY} if KEY else {})
        try:
            _last[0] = time.time()
            with urllib.request.urlopen(req, timeout=60) as r:
                return json.loads(r.read().decode("utf-8"))
        except urllib.error.HTTPError as e:
            body = e.read().decode("utf-8", "replace")[:300]
            sys.stderr.write(f"[HTTP {e.code}] attempt {attempt+1} {path} :: {body}\n")
            if e.code in (429, 500, 502, 503, 504):
                time.sleep(2 + attempt * 2)
                continue
            raise
        except Exception as e:  # network
            sys.stderr.write(f"[ERR] attempt {attempt+1} {path} :: {e}\n")
            time.sleep(2 + attempt * 2)
    raise RuntimeError(f"gave up: {path}")


def all_citations(pid, fields="title,year,venue,externalIds,abstract,publicationTypes,authors", page=1000):
    out, offset = [], 0
    while True:
        d = get(f"/paper/{pid}/citations", {"fields": fields, "limit": page, "offset": offset})
        data = d.get("data", [])
        out.extend(data)
        nxt = d.get("next")
        if nxt is None or not data:
            break
        offset = nxt
    return out


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "search":
        q = sys.argv[2]
        lim = int(sys.argv[3]) if len(sys.argv) > 3 else 100
        d = get("/paper/search", {"query": q, "limit": lim,
                                  "fields": "title,year,venue,externalIds,citationCount,authors"})
        json.dump(d, sys.stdout, ensure_ascii=False)
    elif cmd == "paper":
        d = get(f"/paper/{sys.argv[2]}", {"fields": "title,year,venue,externalIds,citationCount,referenceCount,authors,abstract"})
        json.dump(d, sys.stdout, ensure_ascii=False)
    elif cmd == "citations":
        json.dump(all_citations(sys.argv[2]), sys.stdout, ensure_ascii=False)
