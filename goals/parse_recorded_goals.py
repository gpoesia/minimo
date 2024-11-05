# Read the file and parse examples
with open('recorded-goals.txt', 'r') as f:
    lines = f.readlines()

# Skip the "statement:" line and empty line
goals = []
in_examples = False
current_example = ""

for line in lines:
    if line.strip() == "examples:":
        in_examples = True
        continue
    
    if in_examples:
        # Handle multi-line examples
        if line.startswith('{'):
            if current_example:
                goals.append(current_example)
            current_example = line.strip()
        else:
            current_example += line.strip()

# Add the last example if exists
if current_example:
    goals.append(current_example)

# Parse the examples to extract only successful attempts (???Y)
successful_goals = [goal for goal in goals if '???Y' in goal]

# Convert string representations of dictionaries to actual dictionaries and extract 'str' values
import json

def fix_json_quotes(s):
    replacements = [
        ("'policy'", '"policy"'),
        ("'str'", '"str"'),
        ("'type'", '"type"'),
        # Match the entire string value portion
        (": '", ': "'),
        ("',", '",'),
        ("'}", '"}')
    ]
    for old, new in replacements:
        s = s.replace(old, new)
    return s

successful_goals = [json.loads(fix_json_quotes(goal))['str'] for goal in successful_goals]

# Create a single dictionary with statement and theorems as a list
formatted_goal = {
    "name": "nat-add-synthetic",
    "theorem": "(= (+ z (s z)) (s (+ z (+ z z))))",
    "solution": successful_goals
}

# Save to JSON file
with open('nat-add-synthetic.json', 'w') as f:
    json.dump({"goals": [formatted_goal]}, f, indent=4)
