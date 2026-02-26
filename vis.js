div.innerHTML = '';
div.style.padding = '10px';
div.style.fontFamily = 'Arial, sans-serif';
div.style.overflowY = 'auto';
div.style.height = '100%';

function fetchTuples(relation) {
    try {
        return relation.tuples().map(t => t._atoms.map(a => a.toString()));
    } catch(e) {
        return [];
    }
}

const users = fetchTuples(User).map(t => t[0]);
const posts = fetchTuples(Post).map(t => t[0]);
const cleanName = str => str ? str.split('$')[0] : '';

let html = `<h2 style="color: #333; font-size: 16px; margin: 0 0 10px 0;">Access Control Panel</h2>`;

html += `<h3 style="color: #4A90E2; border-bottom: 1px solid #4A90E2; font-size: 14px; margin: 10px 0 5px 0;">Users</h3>`;
html += `<div style="display: grid; grid-template-columns: repeat(auto-fill, minmax(150px, 1fr)); gap: 8px;">`;

users.forEach(u => {
    let friendsList = [], blockedList = [], mutedList = [];
    fetchTuples(friends).forEach(t => { if (t[0] === u && t[2].includes('True')) friendsList.push(t[1]); });
    fetchTuples(blocked).forEach(t => { if (t[0] === u && t[2].includes('True')) blockedList.push(t[1]); });
    fetchTuples(muted).forEach(t => { if (t[0] === u && t[2].includes('True')) mutedList.push(t[1]); });

    let isClosed = "False", limit10 = "False", strangerSee = "False";
    fetchTuples(moments_closed).forEach(t => { if(t[0] === u) isClosed = t[1]; });
    fetchTuples(limit_recent_10).forEach(t => { if(t[0] === u) limit10 = t[1]; });
    fetchTuples(stranger_see_recent).forEach(t => { if(t[0] === u) strangerSee = t[1]; });

    html += `
    <div style="border: 1px solid #B3D4FF; border-radius: 6px; padding: 8px; background: #F0F8FF; font-size: 11px;">
        <h4 style="margin: 0 0 5px 0; color: #0056b3;">👤 ${cleanName(u)}</h4>
        <div style="line-height: 1.2;">
            <div><b>Friends:</b> ${friendsList.length > 0 ? friendsList.map(cleanName).join(',') : 'None'}</div>
            <div><b>Blocked:</b> <span style="color:red">${blockedList.length > 0 ? blockedList.map(cleanName).join(',') : 'None'}</span></div>
            <div><b>Muted:</b> <span style="color:orange">${mutedList.length > 0 ? mutedList.map(cleanName).join(',') : 'None'}</span></div>
            <div style="margin-top:4px; border-top: 1px dashed #ccc; padding-top:4px;">
                <b>Closed:</b> ${isClosed.includes('True') ? 'Y' : 'N'} | <b>Lim:</b> ${limit10.includes('True') ? 'Y' : 'N'}
            </div>
        </div>
    </div>`;
});
html += `</div>`;

html += `<h3 style="color: #50E3C2; border-bottom: 1px solid #50E3C2; font-size: 14px; margin: 15px 0 5px 0;">Posts</h3>`;
html += `<div style="display: grid; grid-template-columns: repeat(auto-fill, minmax(150px, 1fr)); gap: 8px;">`;

posts.forEach(p => {
    let authorName = "", vis = "", time = "";
    fetchTuples(author).forEach(t => { if(t[0] === p) authorName = t[1]; });
    fetchTuples(visibility).forEach(t => { if(t[0] === p) vis = t[1]; });
    fetchTuples(timestamp).forEach(t => { if(t[0] === p) time = t[1]; });

    let allowed = [], excluded = [];
    fetchTuples(allowed_viewers).forEach(t => { if(t[0] === p && t[2].includes('True')) allowed.push(t[1]); });
    fetchTuples(excluded_viewers).forEach(t => { if(t[0] === p && t[2].includes('True')) excluded.push(t[1]); });

    let cleanVis = cleanName(vis);
    html += `
    <div style="border: 1px solid #A2F3D6; border-radius: 6px; padding: 8px; background: #E6F4EA; font-size: 11px;">
        <h4 style="margin: 0 0 5px 0; color: #28a745;">📝 ${cleanName(p)}</h4>
        <div style="line-height: 1.2;">
            <b>Auth:</b> ${cleanName(authorName)} | <b>Time:</b> ${cleanName(time)}<br>
            <b>Vis:</b> ${cleanVis}
            ${cleanVis.includes('SpecificFriends') ? `<div style="color:#555"><b>Allow:</b> ${allowed.length > 0 ? allowed.map(cleanName).join(',') : 'None'}</div>` : ''}
            ${cleanVis.includes('ExcludeFriends') ? `<div style="color:red"><b>Excl:</b> ${excluded.length > 0 ? excluded.map(cleanName).join(',') : 'None'}</div>` : ''}
        </div>
    </div>`;
});
html += `</div>`;

div.innerHTML = html;