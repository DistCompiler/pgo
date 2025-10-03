CREATE TABLE IF NOT EXISTS config (
    id VARCHAR PRIMARY KEY,
    expected_experiment_count INTEGER,
);

CREATE TABLE IF NOT EXISTS experiment (
    config_id VARCHAR,
    idx INTEGER,
    github VARCHAR,
    branch VARCHAR,
    spec_path VARCHAR,
    mc_spec_path VARCHAR,
    mc_config_path VARCHAR,
    start_time TIMESTAMP,
    end_time TIMESTAMP,
    PRIMARY KEY (config_id, idx),
);

CREATE TABLE IF NOT EXISTS trace (
    config_id VARCHAR,
    experiment_idx INTEGER,
    id integer,
    trace BYTEA,
    PRIMARY KEY (config_id, experiment_idx, id),
    FOREIGN KEY (config_id, experiment_idx) REFERENCES experiment(config_id, idx),
);

CREATE TABLE IF NOT EXISTS gather_log (
    config_id VARCHAR,
    experiment_idx INTEGER,
    name VARCHAR,
    text VARCHAR,
    PRIMARY KEY (config_id, experiment_idx, name),
    FOREIGN KEY (config_id, experiment_idx) REFERENCES experiment(config_id, idx),
);

CREATE TABLE IF NOT EXISTS validation (
    config_id VARCHAR,
    experiment_idx INTEGER,
    log_txt VARCHAR,
    start_time TIMESTAMP,
    end_time TIMESTAMP,
    success BOOLEAN,
    counter_example_bin BYTEA,
    PRIMARY KEY (config_id, experiment_idx),
    FOREIGN KEY (config_id, experiment_idx) REFERENCES experiment(config_id, idx),
    CONSTRAINT fail_has_counterexample CHECK (
        CASE
            WHEN success THEN counter_example_bin IS NULL
            WHEN NOT success THEN counter_example_bin IS NOT NULL
        END
    )
);
