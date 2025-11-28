#!/usr/bin/env bash

set -e -x

cat ../mongoresearch.key.json | docker login -u _json_key https://us-central1-docker.pkg.dev --password-stdin

docker buildx build . -f Dockerfile.config -t wiredtiger-config:antithesis
docker buildx build . -f Dockerfile.test -t wiredtiger:antithesis

docker tag wiredtiger:antithesis us-central1-docker.pkg.dev/molten-verve-216720/mongoresearch-repository/wiredtiger:antithesis
docker tag wiredtiger-config:antithesis us-central1-docker.pkg.dev/molten-verve-216720/mongoresearch-repository/wiredtiger-config:antithesis

docker push us-central1-docker.pkg.dev/molten-verve-216720/mongoresearch-repository/wiredtiger:antithesis
docker push us-central1-docker.pkg.dev/molten-verve-216720/mongoresearch-repository/wiredtiger-config:antithesis

curl --fail -u "$(cat ../mongoresearch.user.txt):$(cat ../mongoresearch.password.txt)" \
    -X POST https://mongoresearch.antithesis.com/api/v1/launch/basic_test \
    -d '{"params": { "antithesis.description":"wiredtiger POC",
        "antithesis.duration":"30",
        "antithesis.config_image":"wiredtiger-config:antithesis",
        "antithesis.images":"wiredtiger:antithesis", 
        "antithesis.report.recipients":"finn.hackett@mongodb.com" } }'
