# Social Media Visibility Model

## Project Objective
In this project, we modeled a social media post system inspired by platforms like WeChat Moments. Our goal is to use Forge to prove that complex privacy settings (like "block this user" or "only show recent 10 posts") work together safely without any data leaks.

## Model Design and Visualization
We designed a multi-layered access control system. We used Forge to map out user relationships (friends, blocklists, mutelists) and post rules. To handle the "recent 10 posts" rule, we used integer timestamps to sort the posts. 

Because the default Forge graph is messy and hard to read, we wrote a custom visualization script. It generates a clean dashboard: the top row shows user settings, and the bottom row shows post details.

## Signatures and Predicates

**Core Signatures:**
* **`User`**: Represents an account, its friends, blocked/muted lists, and global settings.
* **`Post`**: Represents a post, its author, timestamp, and visibility rules.
* **`Visibility`**: Types of privacy (Public, FriendsOnly, SpecificFriends, ExcludeFriends, Private).

**Core Predicates:**
* **`wellformed`**: Basic rules (e.g., you cannot be friends with yourself, blocking someone removes them from friends).
* **`isRecent`**: Checks if a post is within the author's 10 newest posts.
* **`canSee`**: The main logic that decides if a viewer has the right to see a specific post.
* **`known_scenario`**: A sample situation with 4 users to show how all the rules work together.

## Testing
To verify our model, we used Bounded Model Checking. We wrote tests to make sure our logic is strict and secure under all edge cases:
* **Structural Tests**: Check basic rules (e.g., a blocked user cannot be a friend, and a user cannot mute themselves).
* **Access Control Tests**: Prove that privacy rules work correctly in extreme cases (e.g., blocked or muted users absolutely cannot see posts, friends cannot see private posts, and strangers are completely blocked if the global setting is turned off).
* **Time Limit Tests**: Ensure the "recent 10 posts" rule successfully hides older posts from both friends and strangers.

## Documentation
* `social_visibility.frg`: The core Forge model. It defines the structural signatures and calculates the final access permissions.
* `social_visibility.test.frg`: The test suite. It contains tests for basic constraints and real-world edge cases.
* `vis.js`: The custom visualization script. It parses the data and generates the dashboard.