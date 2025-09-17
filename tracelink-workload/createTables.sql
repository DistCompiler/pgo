CREATE SEQUENCE IF NOT EXISTS id_sequence;

CREATE TABLE IF NOT EXISTS experiment (
    id integer PRIMARY KEY DEFAULT nextval('id_sequence'),
    github VARCHAR,
    branch VARCHAR,
    start_time TIMESTAMP,
    end_time TIMESTAMP,
);

CREATE TABLE IF NOT EXISTS trace (
    id integer PRIMARY KEY DEFAULT nextval('id_sequence'),
    experiment_id integer REFERENCES experiment(id),
    trace BYTEA,
);

CREATE TABLE IF NOT EXISTS gather_log (
    id integer PRIMARY KEY DEFAULT nextval('id_sequence'),
    name VARCHAR,
    experiment_id integer REFERENCES experiment(id),
    text VARCHAR,
);

CREATE TABLE IF NOT EXISTS validation (
    id integer PRIMARY KEY DEFAULT nextval('id_sequence'),
    experiment_id integer REFERENCES experiment(id),
    log_txt VARCHAR,
    counter_example_bin BYTEA,
);
