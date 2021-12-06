import os
import sys

from file_read_backwards import FileReadBackwards

files = os.listdir("logs")
elapsed_times = {}
for f in files:
    with FileReadBackwards("logs/" + f, encoding="utf-8") as frb:
        # getting lines by lines starting from the last line up
        end_value = None
        elapsed = None
        while True:
            line = frb.readline()
            if not line:
                break
            line_split = line.split(':')
            value = line_split[2]
            if end_value is not None and value != end_value:
                break
            end_value = value
            elapsed = int(line_split[0])

        elapsed_times[elapsed] = end_value

print(elapsed_times)

max_elapsed = max(elapsed_times.keys())
converged_value = elapsed_times.get(max_elapsed)
result_file = open("results.txt", "a")
result_file.write(str(len(files)) + ":" + str(max_elapsed) + ":" + converged_value)
result_file.close()



