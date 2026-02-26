## Project Objective
In this project, we modeled a social media post system, inspired by social media platforms like WeChat Moments. We're interested in system security, and we can find that it's really complex behind the simple UI toggles (like "only show my last 10 posts" or "block this user"). Our goal was to see if we not only could use Forge to prove that these rules don't contradict each other but also keep data secure.

## Model Design and Visualization
In our model design, we utilize Forge's relational logic to represent a multi-layered access control system. We used partial functions and boolean relations to represent both symmetric connections, like friend lists, and asymmetric connections, like blocklists. To implement the rule of visibility of the most recent 10 posts, we used integer timestamps. This can establish a chronological order and filter posts mathematically while remaining within Forge's bounded integer limits. 

For visualization, the default graph output becomes a highly cluttered and unreadable web. So, our script will generarte a clean dashboard interface. It will display two rows of cards. The top row shows all existing users' info, including their friends, blocked accounts, and global settings. The bottom row shows the post info, including their authors, timestamps, and visibility constraints.

## Signatures and Predicates


## Testing


## Documentation
social_visibility.frg: The core Forge model. It defines the structural signatures and calculates the final access permissions.

social_visibility.test.frg: The test suite. It contains structural tests for basic constraints and property tests for real-world edge cases.

vis.js: The custom visualization script. It parses the data from the Sterling instance and generates the dashboard.