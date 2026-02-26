// vis.js
// 每次执行前清空画板
div.innerHTML = '';
div.style.padding = '20px';
div.style.fontFamily = 'Arial, sans-serif';
div.style.overflow = 'scroll';

// 辅助函数：安全抓取关系的元组 (tuples)
function fetchTuples(relation) {
    try {
        return relation.tuples().map(t => t._atoms.map(a => a.toString()));
    } catch(e) {
        return [];
    }
}

// 提取系统中的核心实体
const users = fetchTuples(User).map(t => t[0]);
const posts = fetchTuples(Post).map(t => t[0]);

let html = `<h2 style="color: #333;">Social Visibility Access Control Panel</h2>`;

// ==========================================
// 渲染 Users 卡片
// ==========================================
html += `<h3 style="color: #4A90E2; border-bottom: 2px solid #4A90E2; padding-bottom: 5px;">Users & Settings</h3>`;
html += `<div style="display: flex; gap: 15px; flex-wrap: wrap; margin-bottom: 30px;">`;

users.forEach(u => {
    // 提取当前用户的配置与关系
    let friendsList = [];
    fetchTuples(friends).forEach(t => {
        // Froglet 里的 pfunc User -> Boolean 解析出来是三元组 [User, User, Boolean]
        if (t[0] === u && t[2].includes('True')) friendsList.push(t[1]);
    });

    let isClosed = "False", limit10 = "False", strangerSee = "False";
    fetchTuples(moments_closed).forEach(t => { if(t[0] === u) isClosed = t[1]; });
    fetchTuples(limit_recent_10).forEach(t => { if(t[0] === u) limit10 = t[1]; });
    fetchTuples(stranger_see_recent).forEach(t => { if(t[0] === u) strangerSee = t[1]; });

    html += `
    <div style="border: 1px solid #B3D4FF; border-radius: 8px; padding: 15px; width: 220px; background: #F0F8FF; box-shadow: 0 2px 4px rgba(0,0,0,0.1);">
        <h4 style="margin: 0 0 10px 0; color: #0056b3; font-size: 18px;">👤 ${u}</h4>
        <div style="font-size: 13px; line-height: 1.6;">
            <div><b>Friends:</b> ${friendsList.length > 0 ? friendsList.join(', ') : '<span style="color:#999">None</span>'}</div>
            <hr style="border: 0; border-top: 1px solid #ccc; margin: 8px 0;">
            <div><b>Moments Closed:</b> <span style="color: ${isClosed.includes('True') ? 'red' : 'green'}">${isClosed.split('$')[0]}</span></div>
            <div><b>Limit Recent 10:</b> ${limit10.split('$')[0]}</div>
            <div><b>Stranger Can See:</b> ${strangerSee.split('$')[0]}</div>
        </div>
    </div>`;
});
html += `</div>`;

// ==========================================
// 渲染 Posts 卡片
// ==========================================
html += `<h3 style="color: #50E3C2; border-bottom: 2px solid #50E3C2; padding-bottom: 5px;">Posts</h3>`;
html += `<div style="display: flex; gap: 15px; flex-wrap: wrap;">`;

posts.forEach(p => {
    let authorName = "", vis = "", time = "";
    fetchTuples(author).forEach(t => { if(t[0] === p) authorName = t[1]; });
    fetchTuples(visibility).forEach(t => { if(t[0] === p) vis = t[1]; });
    fetchTuples(timestamp).forEach(t => { if(t[0] === p) time = t[1]; });

    let allowed = [];
    fetchTuples(allowed_viewers).forEach(t => {
        if(t[0] === p && t[2].includes('True')) allowed.push(t[1]);
    });

    // 清理一下 Forge 命名后缀 (如 Public$0)
    let cleanVis = vis.split('$')[0];

    html += `
    <div style="border: 1px solid #A2F3D6; border-radius: 8px; padding: 15px; width: 220px; background: #E6F4EA; box-shadow: 0 2px 4px rgba(0,0,0,0.1);">
        <h4 style="margin: 0 0 10px 0; color: #28a745; font-size: 16px;">📝 ${p}</h4>
        <div style="font-size: 13px; line-height: 1.6;">
            <div><b>Author:</b> 👤 ${authorName}</div>
            <div><b>Time:</b> ⏱️ ${time}</div>
            <div><b>Visibility:</b> 🔒 ${cleanVis}</div>
            ${cleanVis === 'SpecificFriends' ? `<div><b>Allowed:</b> ${allowed.length > 0 ? allowed.join(', ') : 'None'}</div>` : ''}
        </div>
    </div>`;
});
html += `</div>`;

// 将生成的 HTML 注入到 Sterling 提供的画板中
div.innerHTML = html;