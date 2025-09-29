CREATE TABLE IF NOT EXISTS experiment (
    id VARCHAR,
    github VARCHAR,
    branch VARCHAR,
    spec_path VARCHAR,
    mc_spec_path VARCHAR,
    mc_config_path VARCHAR,
    start_time TIMESTAMP,
    end_time TIMESTAMP,
    PRIMARY KEY (id),
);

CREATE TABLE IF NOT EXISTS trace (
    experiment_id VARCHAR,
    id integer,
    trace BYTEA,
    PRIMARY KEY (experiment_id, id),
    FOREIGN KEY (experiment_id) REFERENCES experiment(id),
);

CREATE TABLE IF NOT EXISTS gather_log (
    experiment_id VARCHAR,
    name VARCHAR,
    text VARCHAR,
    PRIMARY KEY (experiment_id, name),
    FOREIGN KEY (experiment_id) REFERENCES experiment(id),
);

CREATE TABLE IF NOT EXISTS validation (
    experiment_id VARCHAR,
    log_txt VARCHAR,
    start_time TIMESTAMP,
    end_time TIMESTAMP,
    success BOOLEAN,
    counter_example_bin BYTEA,
    PRIMARY KEY (experiment_id),
    FOREIGN KEY (experiment_id) REFERENCES experiment(id),
    CONSTRAINT fail_has_counterexample CHECK (
        CASE
            WHEN success THEN counter_example_bin IS NULL
            WHEN NOT success THEN counter_example_bin IS NOT NULL
        END
    )
);
