build:
    lake build

build-docs:
    lake -R -Kenv=dev build CKMath:docs

serve-docs:
    caddy file-server --listen :1234 --root .lake/build/doc/

format:
    jq . lake-manifest.json > lake-manifest.json.copy
    mv lake-manifest.json.copy lake-manifest.json
