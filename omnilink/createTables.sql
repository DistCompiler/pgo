CREATE TABLE IF NOT EXISTS config (
    id VARCHAR PRIMARY KEY,
    expected_experiment_count INTEGER,
);

CREATE TABLE IF NOT EXISTS experiment (
    config_id VARCHAR,
    idx INTEGER,
    spec_path VARCHAR,
    mc_spec_path VARCHAR,
    mc_config_path VARCHAR,
    start_time TIMESTAMP NOT NULL,
    end_time TIMESTAMP NOT NULL,
    PRIMARY KEY (config_id, idx),
);

ALTER TABLE experiment
    ADD COLUMN IF NOT EXISTS rr_zip BYTEA;
ALTER TABLE experiment
    ADD COLUMN IF NOT EXISTS exit_code INTEGER DEFAULT 0;

CREATE TABLE IF NOT EXISTS trace (
    config_id VARCHAR,
    experiment_idx INTEGER,
    id integer,
    trace BYTEA NOT NULL,
    PRIMARY KEY (config_id, experiment_idx, id),
    FOREIGN KEY (config_id, experiment_idx) REFERENCES experiment(config_id, idx),
);

CREATE TABLE IF NOT EXISTS gather_log (
    config_id VARCHAR,
    experiment_idx INTEGER,
    name VARCHAR NOT NULL,
    text VARCHAR NOT NULL,
    PRIMARY KEY (config_id, experiment_idx, name),
    FOREIGN KEY (config_id, experiment_idx) REFERENCES experiment(config_id, idx),
);

CREATE TABLE IF NOT EXISTS validation (
    config_id VARCHAR,
    experiment_idx INTEGER,
    log_txt VARCHAR NOT NULL,
    start_time TIMESTAMP NOT NULL,
    end_time TIMESTAMP NOT NULL,
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
