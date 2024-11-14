#!/bin/bash

pip install "dstack[all]" -U

mkdir ~/.dstack/ ~/.dstack/server/

#Adjusts /.dstack/server/config.yml as needed
cat > ~/.dstack/server/config.yml <<EOL
projects:
  - name: pdoom
    backends:
      - type: aws
        creds:
          type: access_key
          access_key:  your_access_token <------------------------------------ REPLACE 
          secret_key:  your_secret_token <------------------------------------ REPLACE 
EOL

#Runs the server.
dstack server