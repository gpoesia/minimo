#TO RUN THE FLEET after runinng the server: 

# Adjust ~/.dstack/config.yml file
cat > ~/.dstack/config.yml <<EOL
projects:
- default: true
  name: pdoom
  token: your_admin_token <------------------------------------ REPLACE with admin token that you'll see upon launching the server
  url: http://127.0.0.1:3000
repos: []
EOL

#Initializes
dstack init

# Run dstack apply in the current terminal
dstack apply -f .dstack.yml

#For further dstack command interractions refer to: https://dstack.ai/docs/reference/cli/