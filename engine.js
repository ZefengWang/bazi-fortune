"use strict";

/* =====================================================================
 * 八字命理排盘引擎（全球全历史·高精度演示版）
 * 仅供学习研究使用，严禁商用。
 * 关键能力：
 *   1) 时区→UTC 自动换算（IANA 时区，浏览器 Intl 原生处理夏令时）
 *   2) 节气（立春换年 / 以节定月）—— VSOP 近似算法，精度秒级
 *   3) 真太阳时纠正（经度 + 均时差）
 *   4) 地支藏干 + 加权身强弱判断 + 喜用神方向
 * 说明：排盘基准统一为「绝对 UTC 儒略日」，时区仅影响本地钟表读数。
 * =====================================================================
 */

/* ---------------- 0. 通用算子 ---------------- */
const floordiv = (a, b) => Math.floor(a / b);          // Python // 语义
const pymod = (a, n) => ((a % n) + n) % n;             // Python % 语义（恒非负）
const norm360 = d => ((d % 360) + 360) % 360;          // 角度归一化 [0,360)
const normDelta = d => { d = norm360(d); return d > 180 ? d - 360 : d; }; // 归一到 [-180,180]

/* ---------------- 1. 符号集与属性矩阵 ---------------- */
const TIANGAN = ["甲","乙","丙","丁","戊","己","庚","辛","壬","癸"];
const DIZHI   = ["子","丑","寅","卯","辰","巳","午","未","申","酉","戌","亥"];

const WU_XING = {
  "甲":"木","乙":"木","丙":"火","丁":"火","戊":"土","己":"土",
  "庚":"金","辛":"金","壬":"水","癸":"水",
  "寅":"木","卯":"木","巳":"火","午":"火","申":"金","酉":"金",
  "亥":"水","子":"水","辰":"土","戌":"土","丑":"土","未":"土"
};
const YIN_YANG = {
  "甲":"阳","丙":"阳","戊":"阳","庚":"阳","壬":"阳",
  "寅":"阳","辰":"阳","午":"阳","申":"阳","戌":"阳","子":"阳",
  "乙":"阴","丁":"阴","己":"阴","辛":"阴","癸":"阴",
  "卯":"阴","巳":"阴","未":"阴","酉":"阴","亥":"阴","丑":"阴"
};

const SHISHEN_MAP = {
  "同|同":"比肩","同|异":"劫财",
  "生我|同":"偏印","生我|异":"正印",
  "我生|同":"食神","我生|异":"伤官",
  "克我|同":"七杀","克我|异":"正官",
  "我克|同":"偏财","我克|异":"正财"
};

/* 地支藏干（主气 / 中气 / 余气） */
const HIDDEN_STEMS = {
  "子":["癸"],
  "丑":["己","癸","辛"],
  "寅":["甲","丙","戊"],
  "卯":["乙"],
  "辰":["戊","乙","癸"],
  "巳":["丙","戊","庚"],
  "午":["丁","己"],
  "未":["己","丁","乙"],
  "申":["庚","壬","戊"],
  "酉":["辛"],
  "戌":["戊","辛","丁"],
  "亥":["壬","甲"]
};
/* 藏干力量权重（本气/中气/余气，单藏干记 100） */
const HIDDEN_WEIGHT = [100, 60, 30];

/* 中国省级经度回退表（已由 cities-data.js 取代，此处保留兜底） */
const PROVINCE_FALLBACK_LNG = {
  "北京市":116.40,"上海市":121.47,"天津市":117.20,"重庆市":106.54,
  "河北省":114.48,"山西省":112.53,"辽宁省":123.38,"吉林省":125.35,
  "黑龙江省":126.63,"江苏省":118.78,"浙江省":120.15,"安徽省":117.27,
  "福建省":119.30,"江西省":115.89,"山东省":117.00,"河南省":113.65,
  "湖北省":114.31,"湖南省":112.98,"广东省":113.26,"海南省":110.35,
  "四川省":104.06,"贵州省":106.71,"云南省":102.73,"陕西省":108.95,
  "甘肃省":103.73,"青海省":101.74,"台湾省":121.50,
  "内蒙古自治区":111.65,"广西壮族自治区":108.33,"西藏自治区":91.11,
  "宁夏回族自治区":106.27,"新疆维吾尔自治区":87.68
};

/* ---------------- 2. 历法与天文学 ---------------- */
function is_valid_date(year, month, day) {
  if (month < 1 || month > 12 || day < 1) return false;
  const astronomical_year = year > 0 ? year : year + 1;
  let is_leap;
  if (astronomical_year < 1582) {
    is_leap = (astronomical_year % 4 === 0);
  } else {
    is_leap = (astronomical_year % 4 === 0 && astronomical_year % 100 !== 0)
      || (astronomical_year % 400 === 0);
  }
  const days_in_month = [31, is_leap ? 29 : 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
  if (year === 1582 && month === 10 && day >= 5 && day <= 14) return false;
  return day <= days_in_month[month - 1];
}

/* 公历（格列历）→ 儒略日（含时分小数） */
function date_to_julian_day(year, month, day, hour = 0, minute = 0) {
  if (year < 0) year = year + 1;
  if (month <= 2) { year -= 1; month += 12; }
  let B;
  if ((year > 1582) || (year === 1582 && month > 10) || (year === 1582 && month === 10 && day >= 15)) {
    const A = floordiv(year, 100);
    B = 2 - A + floordiv(A, 4);
  } else {
    B = 0;
  }
  let jd = Math.floor(365.25 * (year + 4716)) + Math.floor(30.6001 * (month + 1)) + day + B - 1524.5;
  jd += (hour + minute / 60.0) / 24.0;
  return jd;
}

/* ΔT = TT - UT（秒），用于把力学时转成世界时。NASA 多项式分段表。 */
function deltaT(year) {
  const T = [
    [-4000,108371.7,-13036.80,392.000,0.0000],[-500,17201.0,-627.82,16.170,-0.3413],
    [-150,12200.6,-346.41,5.403,-0.1593],[150,9113.8,-328.13,-1.647,0.0377],
    [500,5707.5,-391.41,0.915,0.3145],[900,2203.4,-283.45,13.034,-0.1778],
    [1300,490.1,-57.35,2.085,-0.0072],[1600,120.0,-9.81,-1.532,0.1403],
    [1700,10.2,-0.91,0.510,-0.0370],[1800,13.4,-0.72,0.202,-0.0193],
    [1830,7.8,-1.81,0.416,-0.0247],[1860,8.3,-0.13,-0.406,0.0292],
    [1880,-5.4,0.32,-0.183,0.0173],[1900,-2.3,2.06,0.169,-0.0135],
    [1920,21.2,1.69,-0.304,0.0167],[1940,24.2,1.22,-0.064,0.0031],
    [1960,33.2,0.51,0.231,-0.0109],[1980,51.0,1.29,-0.026,0.0032],
    [2000,63.87,0.1,0,0]
  ];
  let i = 0;
  for (let k = 0; k < T.length; k++) if (year >= T[k][0]) i = k;
  if (i === T.length - 1) { // 2000 年后外推
    const y = year;
    if (y <= 2014) return 64.7 + (y - 2005) * 0.4;
    const f = yy => -20 + 31 * Math.pow((yy - 1820) / 100, 2);
    const F2014 = 64.7 + (2014 - 2005) * 0.4;
    if (y >= 2114) return f(y);
    return f(y) - (2114 - y) * (f(2014) - F2014) / 100;
  }
  const [Y1, a, b, c, d] = T[i], Y2 = T[i + 1][0];
  const t1 = (year - Y1) / (Y2 - Y1) * 10, t2 = t1 * t1, t3 = t2 * t1;
  return a + b * t1 + c * t2 + d * t3;
}

/* 太阳视黄经（度，几何平黄经 + VSOP 主要摄动项）。t 为 TT 儒略世纪。 */
function solarLongitudeDeg(t) {
  const t2 = t * t, t3 = t2 * t, t4 = t3 * t;
  let L = 48950621.66 + 6283319653.318 * t + 52.9674 * t2 + 0.00432 * t3 - 0.001124 * t4
    + 334166 * Math.cos(4.669257 + 628.307585 * t)
    + 3489 * Math.cos(4.6261 + 1256.61517 * t)
    + 350 * Math.cos(2.744 + 575.3385 * t)
    + 342 * Math.cos(2.829 + 0.3523 * t)
    + 314 * Math.cos(3.628 + 7771.3771 * t)
    + 268 * Math.cos(4.418 + 786.0419 * t)
    + 234 * Math.cos(6.135 + 393.021 * t)
    + 132 * Math.cos(0.742 + 1150.677 * t)
    + 127 * Math.cos(2.037 + 52.9691 * t)
    + 120 * Math.cos(1.11 + 157.7344 * t)
    + 99 * Math.cos(5.23 + 588.493 * t)
    + 90 * Math.cos(2.05 + 2.63 * t)
    + 86 * Math.cos(3.51 + 39.815 * t)
    + 78 * Math.cos(1.18 + 522.369 * t)
    + 75 * Math.cos(2.53 + 550.755 * t)
    + 51 * Math.cos(4.58 + 1884.923 * t)
    + 49 * Math.cos(4.21 + 77.552 * t)
    + 36 * Math.cos(2.92 + 0.07 * t)
    + 32 * Math.cos(5.85 + 1179.063 * t)
    + 28 * Math.cos(1.9 + 79.63 * t)
    + 27 * Math.cos(0.31 + 1097.71 * t)
    + 2060.6 * Math.cos(2.67823 + 628.307585 * t) * t
    + 43.0 * Math.cos(2.635 + 1256.6152 * t) * t
    + 8.72 * Math.cos(1.072 + 628.3076 * t) * t2
    - 994 - 834 * Math.sin(2.1824 - 33.75705 * t)
    - 64 * Math.sin(3.5069 + 1256.66393 * t);
  return norm360((L / 10000000) * 180 / Math.PI);
}

// 24 节气近似日期（公历月/日），用于二分初值
const APPROX = [[2,4],[2,19],[3,6],[3,21],[4,5],[4,20],[5,6],[5,21],[6,6],[6,21],[7,7],[7,23],[8,8],[8,23],[9,8],[9,23],[10,8],[10,23],[11,7],[11,22],[12,7],[12,22],[1,6],[1,20]];
const TERM_NAMES = ["立春","雨水","惊蛰","春分","清明","谷雨","立夏","小满","芒种","夏至","小暑","大暑","立秋","处暑","白露","秋分","寒露","霜降","立冬","小雪","大雪","冬至","小寒","大寒"];

/**
 * 求某年第 i 个节气（i: 0=立春 …… 23=大寒）发生的绝对 UT 儒略日。
 * 二分法解太阳视黄经 = 315 + 15·i 的时刻，精度秒级。
 */
function solarTermUtJd(year, i) {
  const W = norm360(315 + 15 * i);
  const [mo, dy] = APPROX[i];
  const tApp = (date_to_julian_day(year, mo, dy) - 2451545) / 36525;
  let lo = tApp - 0.0001, hi = tApp + 0.0001;   // ±3.65 天
  let flo = normDelta(solarLongitudeDeg(lo) - W);
  let fhi = normDelta(solarLongitudeDeg(hi) - W);
  if (flo > fhi) { [lo, hi] = [hi, lo]; [flo, fhi] = [fhi, flo]; }
  for (let k = 0; k < 60; k++) {
    const mid = (lo + hi) / 2;
    if (normDelta(solarLongitudeDeg(mid) - W) >= 0) hi = mid; else lo = mid;
  }
  const t = (lo + hi) / 2;
  const dt = deltaT(year);
  return 2451545 + t * 36525 - dt / 86400;      // 绝对 UT 儒略日
}

/* 均时差（分钟）：真太阳时 = 平太阳时 + EoT。近似公式，误差 < 30 秒。 */
function equationOfTime(year, month, day) {
  const astro_year = year > 0 ? year : year + 1;
  let is_leap;
  if (astro_year < 1582) is_leap = (astro_year % 4 === 0);
  else is_leap = (astro_year % 4 === 0 && astro_year % 100 !== 0) || (astro_year % 400 === 0);
  const dim = [31, is_leap ? 29 : 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
  const n_days = dim.slice(0, month - 1).reduce((s, x) => s + x, 0) + day;
  const b_rad = 2 * Math.PI * (n_days - 81) / 364;
  return 9.87 * Math.sin(2 * b_rad) - 7.53 * Math.cos(b_rad) - 1.5 * Math.sin(b_rad);
}

/* ---------------- 3. 时区 ---------------- */
const _dtfCache = Object.create(null);

/* 获取某 UTC 时刻（毫秒）在指定 IANA 时区的偏移量（毫秒，东正西负） */
function getTimeZoneOffsetMs(ts, timeZone) {
  let dtf = _dtfCache[timeZone];
  if (!dtf) {
    try {
      dtf = new Intl.DateTimeFormat("en-US", {
        timeZone,
        year: "numeric", month: "2-digit", day: "2-digit",
        hour: "2-digit", minute: "2-digit", second: "2-digit", hourCycle: "h23"
      });
    } catch (e) {
      throw new Error("无效的时区标识：" + timeZone);
    }
    _dtfCache[timeZone] = dtf;
  }
  const parts = {};
  for (const p of dtf.formatToParts(ts)) parts[p.type] = p.value;
  const y = +parts.year, mo = +parts.month, d = +parts.day;
  const h = +parts.hour, mi = +parts.minute, s = +parts.second;
  const asUTC = Date.UTC(y, mo - 1, d, h, mi, s);
  return asUTC - ts;
}

/* 稳妥构造"年份 y-mo-d h:mi:s"对应的 UTC 毫秒（处理 0-99 年 Date.UTC 怪癖） */
function dateToMsUtc(y, mo, d, h, mi) {
  let ms = Date.UTC(y, mo - 1, d, h, mi, 0);
  if (y >= 0 && y <= 99) {
    const dt = new Date(ms);
    dt.setUTCFullYear(y);
    ms = dt.getTime();
  }
  return ms;
}

/* 当地钟表时间 → UTC 毫秒。固定点迭代收敛夏令时边界（折叠歧义 1 小时除外）。 */
function localToUtcMs(y, mo, d, h, mi, timeZone) {
  const localMs = dateToMsUtc(y, mo, d, h, mi);
  let ts = localMs;
  for (let i = 0; i < 2; i++) {
    ts = localMs - getTimeZoneOffsetMs(ts, timeZone);
  }
  return ts;
}

/* 获取该时区"标准时间（非夏令时）"的固定偏移（分钟，东正西负）。
 * 原理：对同一年取 12 个代表日（每月 15 日）求偏移，取其中的"最小值"
 * （夏令时总是让偏移增大 60 分钟，故全年偏移最小值即标准时间基准偏移），
 * 避免被出生日期是否处于 DST 影响。
 * 用于"输入时间为标准时间、不自动套夏令时"的用户选项（默认）。 */
function getStandardOffsetMin(timeZone) {
  let min = Infinity;
  for (let mo = 1; mo <= 12; mo++) {
    const y = 2024, d = 15, h = 12, mi = 0;
    const lms = dateToMsUtc(y, mo, d, h, mi);
    let ts = lms;
    for (let i = 0; i < 2; i++) ts = lms - getTimeZoneOffsetMs(ts, timeZone);
    const off = Math.round((lms - ts) / 60000);
    if (off < min) min = off;
  }
  return min;
}

const msToJd = ms => ms / 86400000 + 2440587.5;

/* ---------------- 4. 格局详解数据 ---------------- */
const PATTERN_DETAILS = {
  "正财": {
    "名称":"正财格",
    "生克路径":"日主力量去驾驭月令的务实财富（我克者为财）。需要日主自身有根基，方能担财。",
    "性格双重拆解":"显性：做事极有条理，金钱观务实，重视风险控制；隐性：有时过于斤斤计较，缺乏冒险精神，容易错失以小博大的机会。",
    "事业天花板":"适合在成熟体制、金融机构、实业供应链中担任核心管理或财务统筹，走稳健晋升路线。",
    "核心用神解法":"若全盘克泄过多导致身弱，最喜【正印/比肩】运来生扶抗财；若身强财轻，则喜【食神】来引通聪慧，源源不断生财。"
  },
  "偏财": {
    "名称":"偏财格",
    "生克路径":"日主与月令财富磁场发生非线性的剧烈碰撞。属于众人之财、流动之财、大财。",
    "性格双重拆解":"显性：豪爽侠义，极具商业敏锐度，擅长资源整合与人际博弈；隐性：风险偏好较高，耐性不足，容易大起大落。",
    "事业天花板":"天然的创业者、职业投资人或高级商务开拓者。不适合死板的打卡工作，天花板取决于资源杠杆的大小。",
    "核心用神解法":"偏财格最怕比劫夺财，若盘中出现劫财，必须有【官杀】护财，或者【食伤】通关，方能守住富贵。"
  },
  "正官": {
    "名称":"正官格",
    "生克路径":"月令对日主实施规范化的正向约束（克我者为官）。这是一种天地正气，代表名誉与正统约束力。",
    "性格双重拆解":"显性：光明磊落，自律性极强，极具社会责任感与行政天赋；隐性：思想容易传统保守，过度在乎外界评价，面对打破常规的变革时显得优柔寡断。",
    "事业天花板":"公职体系、大型跨国企业的核心行政高管、法务合规统筹。能在现有的稳定规则框架内做到行业最高层。",
    "核心用神解法":"官星最怕【伤官】克害（伤官见官）。系统最优解是配以【正印】，形成'官印相生'，则权柄稳固，名利双收。"
  },
  "七杀": {
    "名称":"七杀格",
    "生克路径":"月令对日主实施同极性的猛烈攻伐。这是一把双刃剑，代表剧烈的外部危机、强烈破坏力与变革能量。",
    "性格双重拆解":"显性：杀伐果断，危机处理能力极强，具有不服输的斗志与逆境翻盘的狼性；隐性：疑心较重，带有攻击性，容易让自己长期处于高度紧绷的焦虑状态。",
    "事业天花板":"竞争极度激烈的行业破局者、军警执法高层、或高风险领域的总指挥。往往在危机或行业洗牌中脱颖而出。",
    "核心用神解法":"七杀必须有制化方能为我所用。最优解有两种：一是用【食神】从正面硬撼压制（食神制杀）；二是用【正印】从侧面感化吸收（杀印相生）。"
  },
  "正印": {
    "名称":"正印格",
    "生克路径":"月令能量源源不断地无私输入、生扶日主（生我者为印）。代表母亲、福报、学术信仰与全方位的保护伞。",
    "性格双重拆解":"显性：心地慈悲，求知欲极强，具有极高的包容力与奉献精神，天然得长辈器重；隐性：容易陷入空想，行动力偏弱，在残酷的商业竞争中显得过于天真和书生气。",
    "事业天花板":"高校教授、核心科研人员、文化出版巨头、或慈善医疗机构负责人。适合走依靠声誉、思想和专业壁垒的持久路线。",
    "核心用神解法":"印星太重容易让人懒散。系统最喜【财星】来适度克制（财星配印），以物欲激活行动力；但切忌贪财坏印。"
  },
  "偏印": {
    "名称":"偏印格（枭神格）",
    "生克路径":"月令对日主实施同极性的非对称输入。这是一种剑走偏锋的领悟力，代表冷门知识、特异直觉与孤独深邃的能量。",
    "性格双重拆解":"显性：直觉惊人，能一眼看穿事物的漏洞，多才多艺，在特定偏门领域具备独特天赋；隐性：性格孤僻敏感，不易信任他人，内心深处常有强烈的疏离感与虚无感。",
    "事业天花板":"顶级研发人员、心理学专家、尖端科技开拓者、或者特立独行的艺术创作者。在别人少走的冷门细分赛道形成独特优势。",
    "核心用神解法":"偏印格最怕'枭神夺食'（即偏印克制食神、才华受阻）。系统极度渴望【偏财】来强势制约偏印，通关释放食神能量。"
  },
  "食神": {
    "名称":"食神格",
    "生克路径":"日主纯能量的自然流露与向外输出。由于极性相同，输出温和且带有福气，属于'福寿星'。",
    "性格双重拆解":"显性：心态宽和，才华内敛而不张扬，极为注重生活品质、审美与精神自由；隐性：有时流于随性，缺乏危机感，面对高强度的逼迫时容易选择躺平或逃避。",
    "事业天花板":"顶级产品架构师、文创策划者、高端美学、咨询顾问或技术专家。无需与人激烈竞争，靠才华自然吸引机会与提携。",
    "核心用神解法":"食神最喜【财星】顺势流转（食神生财），将才华彻底变现；同时最怕【偏印】暗中克制导致格局受损。"
  },
  "伤官": {
    "名称":"伤官格",
    "生克路径":"日主能量爆发式的、跨极性的强烈输出。这是最狂暴的才华与创造力，天生具有打破常规、颠覆旧体制的叛逆因子。",
    "性格双重拆解":"显性：才华横溢，口才极佳，领悟力惊人，极具创新精神与降维打击的个人魅力；隐性：恃才傲物，说话容易扎人，天生不服管束，容易招惹口舌是非、得罪权贵。",
    "事业天花板":"演艺界巨星、自由职业意见领袖、颠覆性科技项目的核心研发总监、或顶尖投资人。天花板高度取决于其才华被变现的程度。",
    "核心用神解法":"伤官必须驯服。上策是配以【正印】形成'伤官配印'，以理智约束狂气；下策是顺势配以【财星】（伤官生财），转化为红利。"
  },
  "比肩": {
    "名称":"建禄/月劫倾向（独立格）",
    "生克路径":"月令能量与日主完全同气、同质。整个天地磁场在充盈你的自我意识，属于极强的主观能动性之格。",
    "性格双重拆解":"显性：意志极其坚定，自信独立，凡事习惯亲力亲为，极具同业竞争的耐力与骨气；隐性：极为固执，很难听进别人的劝告，有时显得过于独断专行，多竞争分财。",
    "事业天花板":"独立创业者、合伙企业的核心技术领袖、或者竞技、销售等需要高强度竞争的行业开拓者。拼的是扎实的个人能力。",
    "核心用神解法":"满盘同气最容易导致比劫夺财。系统极度需要【官杀】作为高悬的威慑规管；或者配以【食伤】将狂暴力量引导输出。"
  },
  "劫财": {
    "名称":"建禄/月劫倾向（独立格）",
    "生克路径":"月令能量与日主完全同气、同质。整个天地磁场在充盈你的自我意识，属于极强的主观能动性之格。",
    "性格双重拆解":"显性：意志极其坚定，自信独立，凡事习惯亲力亲为，极具同业竞争的耐力与骨气；隐性：极为固执，很难听进别人的劝告，有时显得过于独断专行，多竞争分财。",
    "事业天花板":"独立创业者、合伙企业的核心技术领袖、或者竞技、销售等需要高强度竞争的行业开拓者。拼的是扎实的个人能力。",
    "核心用神解法":"满盘同气最容易导致比劫夺财。系统极度需要【官杀】作为高悬的威慑规管；或者配以【食伤】将狂暴力量引导输出。"
  }
};

const FALLBACK_DETAIL = {
  "名称":"特殊/均衡格",
  "生克路径":"全盘五行力量处于多极平衡状态，未形成单一绝对统治力的能量场。",
  "性格双重拆解":"显性：处事圆融，极具大局观，能在不同派系间游刃有余；隐性：有时缺乏鲜明的个人核心标签，容易陷入多头拉扯的内耗。",
  "事业天花板":"大型复杂跨国项目的高级统筹者、多方利益博弈的调解人或综合性高管。",
  "核心用神解法":"此格不求单点突破，最喜大运走【五行流通】之运，能量不断流则一生安稳，利于平稳发展、逐步积累成果。"
};

/* 十神详解（相对日主）—— 用于命盘十神逐项解读 */
const SHISHEN_DETAILS = {
  "比肩": {
    "含义":"与日主同五行、同阴阳的同类力量，代表兄弟、朋友、同事、竞争者，也代表自我意志与独立人格。",
    "性格":"自尊心强、独立自主、讲义气、重朋友，凡事习惯亲力亲为；但易固执己见、不喜受人管束，竞争意识强烈。",
    "事业":"适合独立创业、技术攻坚、竞技体育、销售等需要个人硬实力的领域；忌与人合伙分利，易因争夺而破财。",
    "喜忌":"身强比肩多者，宜以官杀制之、食伤泄之；身弱则喜比肩帮扶，得朋友兄弟之力。"
  },
  "劫财": {
    "含义":"与日主同五行、异阴阳的力量，代表异姓兄弟姐妹、同事伙伴，也象征破财、争夺与竞争。",
    "性格":"豪爽大方、行动力强、敢于冒险，善于借势；但易冲动消费、好面子、与人争利，钱财难聚。",
    "事业":"适合开拓型、竞争型行业，能快速抢占市场；但需防合伙纠纷、小人夺财，宜建立清晰的分利机制。",
    "喜忌":"劫财旺者最忌身强无制，财来财去；宜配官杀护财、食伤生财，方能聚财守成。"
  },
  "正印": {
    "含义":"生我者、异性，代表母亲、长辈、贵人、学业、名誉与庇护，是命中最温柔的守护力量。",
    "性格":"心地善良、包容宽厚、求知欲强、重视名誉，天然得长辈提携；但易依赖他人、行动力偏弱、思虑过多。",
    "事业":"适合教育、科研、文化、医疗、公益等依靠声誉与专业壁垒的领域，走稳健持久路线。",
    "喜忌":"印星过重则懒散空想，宜以财星适度制印、以食伤泄秀；印星为用则利学业功名，多得贵人。"
  },
  "偏印": {
    "含义":"生我者、同性，代表继母或非亲生长辈、偏门学问、玄学、特异直觉与孤独深邃的能量。",
    "性格":"直觉敏锐、思维独特、多才多艺，能洞察事物本质；但性格孤僻、多疑敏感、易钻牛角尖。",
    "事业":"适合研发、心理学、尖端科技、特立独行的艺术创作等冷门细分领域，易形成专长。",
    "喜忌":"偏印最忌夺食（枭神夺食，即偏印克制食神、才华受阻），需以偏财制之、以食神通关；偏印为用则智慧超群，利偏门成就。"
  },
  "食神": {
    "含义":"我生者、同性，代表才华的自然流露、口福、子女与福气，是命中的'福寿星'。",
    "性格":"心态宽和、才华内敛、热爱生活、注重审美与精神自由；但易随性安逸、缺乏危机感。",
    "事业":"适合产品设计、文创、美学、咨询、美食等靠才华与品味变现的领域，易得口碑与回报。",
    "喜忌":"食神最喜生财，才华可源源变现；最忌偏印克制（枭神夺食），才华受阻、福气受损。"
  },
  "伤官": {
    "含义":"我生者、异性，代表才华的爆发式输出、口才、叛逆与创新，是最狂暴的创造力。",
    "性格":"才华横溢、口才极佳、领悟力惊人、极具个人魅力；但恃才傲物、说话扎人、不服管束、易惹是非。",
    "事业":"适合演艺、自媒体、颠覆性科技、投资等需要创新与表达的领域，易在创新领域脱颖而出。",
    "喜忌":"伤官必须驯服：配正印成'伤官配印'以理智约束才华，或配财星'伤官生财'将才华变现；忌伤官见官。"
  },
  "正官": {
    "含义":"克我者、异性，代表官职、名誉、纪律与正统约束，是天地正气。",
    "性格":"光明磊落、自律性强、责任感重、重名誉讲规矩；但易保守传统、过度在意他人评价。",
    "事业":"适合公职、大型企业高管、法务合规等体制内路线，能在规则框架内做到高层。",
    "喜忌":"官星喜印相生（官印相生）则权柄稳固；最忌伤官克官（伤官见官），仕途多波折。"
  },
  "七杀": {
    "含义":"克我者、同性，代表权力、压力、竞争与变革，是一把双刃剑。",
    "性格":"杀伐果断、魄力十足、危机处理能力强、有逆境翻盘的狼性；但疑心重、攻击性强、易长期紧绷。",
    "事业":"适合竞争激烈行业的破局者、军警、高风险领域总指挥，常在危机中展现担当。",
    "喜忌":"七杀必须有制化：食神制杀（正面硬撼）或正印化杀（杀印相生），方能化压力为权柄。"
  },
  "正财": {
    "含义":"我克者、异性，代表正当财富、稳定收入、妻子（男命）与务实经营。",
    "性格":"务实稳重、精打细算、重视积累、风险意识强；但易过于计较、缺乏冒险精神。",
    "事业":"适合金融、实业、供应链、财务统筹等稳健领域，走踏实积累路线。",
    "喜忌":"身强财旺则富贵可期；身弱财多则担财吃力，宜配印比生扶，方能担财守财。"
  },
  "偏财": {
    "含义":"我克者、同性，代表意外之财、流动之财、父亲、投资理财与人脉资源。",
    "性格":"豪爽侠义、商业嗅觉敏锐、擅长资源整合与人际博弈；但风险偏好较高、耐性不足、易大起大落。",
    "事业":"适合创业、投资、商务开拓等杠杆型领域，财富天花板取决于资源整合能力。",
    "喜忌":"偏财最怕比劫夺财，宜配官杀护财或食伤通关；偏财为用则财路较广，利于开拓新财源。"
  }
};

/* 四柱宫位详解 */
const PILLAR_MEANING = {
  "年柱":{"宫位":"祖上 · 父母 · 早年（约 1-16 岁）","说明":"代表祖荫、原生家庭与早年根基。年干为父辈影响，年支为祖辈环境，也反映少年时期的成长底色。"},
  "月柱":{"宫位":"父母 · 兄弟 · 青年（约 17-32 岁）","说明":"代表父母兄弟与青年运势。月令为格局核心，是命局力量最旺之处，奠定一生大方向与事业起点。"},
  "日柱":{"宫位":"自身 · 婚姻 · 中年（约 33-48 岁）","说明":"日干为日主自身，代表本人核心；日支为婚姻宫，代表配偶与婚姻状态，也主中年运势。"},
  "时柱":{"宫位":"子女 · 晚年（约 49 岁后）","说明":"代表子女、下属与晚年归宿。时支为子女宫，反映晚景与人生收尾的格局。"}
};

/* 十天干日主性格总论（日主为命局核心） */
const TIANGAN_CHARACTER = {
  "甲":{"五行":"阳木","意象":"参天大树、栋梁之材","性格":"正直仁厚、积极向上、有担当与领导力，如大树般向上生长、庇护他人；但易固执要强、不喜低头，压力大时容易硬扛。","特质":"适合开拓进取、独当一面的角色，忌被压抑束缚，喜自由生长空间。"},
  "乙":{"五行":"阴木","意象":"花草藤蔓、柔韧之木","性格":"温和柔韧、灵活变通、善于借势，如藤蔓般能屈能伸、适应力强；但易优柔寡断、依赖他人，缺乏主见时随波逐流。","特质":"适合协调、辅助、策划类工作，善用柔劲化解矛盾，忌硬碰硬。"},
  "丙":{"五行":"阳火","意象":"太阳之火、光明炽热","性格":"热情开朗、光明磊落、感染力强，如太阳般温暖照亮他人；但易急躁冲动、锋芒外露，热情来得快去得也快。","特质":"适合舞台、公关、开拓等需要感染力的领域，忌过度张扬引火烧身。"},
  "丁":{"五行":"阴火","意象":"灯烛之火、星光温润","性格":"细腻敏锐、温和内敛、洞察力强，如灯烛般温暖而专注；但易多愁善感、思虑过重，情绪起伏较内隐。","特质":"适合精细、研究、艺术类工作，善用专注与洞察，忌钻牛角尖。"},
  "戊":{"五行":"阳土","意象":"高山厚土、城墙之土","性格":"稳重踏实、诚信可靠、包容力强，如高山般厚重可依；但易固执保守、反应偏慢，不喜变化与冒险。","特质":"适合管理、金融、实业等需要稳定与信任的领域，忌僵化不知变通。"},
  "己":{"五行":"阴土","意象":"田园沃土、滋养之土","性格":"温和包容、心思细腻、善于滋养成全他人，如田园般默默孕育；但易多虑内耗、缺乏魄力，凡事想得太多。","特质":"适合后勤、教育、服务等滋养型角色，善用耐心与细致，忌过度自我牺牲。"},
  "庚":{"五行":"阳金","意象":"刀剑之金、刚锐肃杀","性格":"刚毅果决、重义气、行动力强，如刀剑般锋利果断；但易锋芒伤人、过于直接，不擅委婉与妥协。","特质":"适合竞争、执法、技术攻坚等硬核领域，忌刚愎自用、树敌过多。"},
  "辛":{"五行":"阴金","意象":"珠玉之金、精致贵重","性格":"精致敏锐、自尊心强、追求品质，如珠玉般温润而贵重；但易敏感挑剔、好面子，对人对己要求过高。","特质":"适合审美、金融、精密技术等讲究品质的领域，忌过度追求完美而内耗。"},
  "壬":{"五行":"阳水","意象":"江河大海、奔流不息","性格":"豁达聪慧、足智多谋、不拘小节，如江河般奔涌向前、包容万物；但易散漫随性、缺乏定性，想法多而落地少。","特质":"适合开拓、贸易、流动性强的领域，善用智慧与变通，忌虎头蛇尾。"},
  "癸":{"五行":"阴水","意象":"雨露泉水、润物无声","性格":"温柔细腻、直觉敏锐、善于以柔克刚，如雨露般无声滋养；但易多疑敏感、内心戏多，遇事容易退缩。","特质":"适合研究、策划、幕后等需要洞察的领域，善用直觉与耐心，忌过度隐忍。"}
};

/* ---------------- 5. 十神 ---------------- */
function get_shishen_relation(me, other) {
  const me_x = WU_XING[me], me_y = YIN_YANG[me];
  const ot_x = WU_XING[other], ot_y = YIN_YANG[other];
  const elements = ["木","火","土","金","水"];
  const dist = pymod(elements.indexOf(ot_x) - elements.indexOf(me_x), 5);
  const relation_map = { 0:"同", 1:"我生", 2:"我克", 3:"克我", 4:"生我" };
  const relation = relation_map[dist];
  const same = (me_y === ot_y) ? "同" : "异";
  return SHISHEN_MAP[relation + "|" + same];
}

/* 地支本气（主气）天干 —— 用于月令格局判定，避免地支阴阳 ≠ 主气干阴阳的偏差 */
function primaryHiddenStem(branch) {
  return HIDDEN_STEMS[branch][0];
}

/* ---------------- 6. 核心排盘 ---------------- */
/**
 * 全球排盘主入口
 * @param number year/month/day/hour/minute  出生地当地钟表时间
 * @param number longitude  出生地经度（东经正、西经负）
 * @param string timezone   IANA 时区（如 "Asia/Shanghai"、"America/New_York"）
 * @param number time_type  1=现代行政时间（自动转真太阳时）；2=古代视太阳时（输入已校准）
 */
function execute_global_fortune_engine(year, month, day, hour, minute, longitude, timezone, time_type, use_dst) {
  let t_year = year, t_month = month, t_day = day, t_hour = hour, t_min = minute;
  let offset_min = 0, eot_min = 0;

  if (time_type === 1) {
    // 1) 时区偏移（分钟，东正西负）。
    const inputMs = dateToMsUtc(year, month, day, hour, minute);
    // use_dst: true=用户声明所填时间为夏令时（按当日真实偏移）；false/未传=标准时间（去掉夏令时）
    const utcMs = use_dst
      ? localToUtcMs(year, month, day, hour, minute, timezone)
      : dateToMsUtc(year, month, day, hour, minute) - getStandardOffsetMin(timezone) * 60000;
    offset_min = Math.round((inputMs - utcMs) / 60000);

    // 2) 均时差
    eot_min = equationOfTime(year, month, day);

    // 3) 真太阳时修正总量：total_delta = (经度×4 + 均时差) - 时区偏移
    //    对国内(offset=480)退化为 (经度-120)×4 + 均时差，与旧算法完全一致。
    const total_delta = (longitude * 4 + eot_min) - offset_min;

    // 4) 由修正后的绝度儒略日反解出"真太阳时读数"的日历（跨日自动进位/退位）
    const approx_jd = date_to_julian_day(year, month, day, hour, minute) + (total_delta / 1440.0);
    const z = Math.floor(approx_jd + 0.5);
    let a;
    if (z < 2299161) a = z;
    else {
      const alpha = floordiv(z - 1867216.25, 36524.25);
      a = z + 1 + alpha - floordiv(alpha, 4);
    }
    const b = a + 1524;
    const c = floordiv(b - 122.1, 365.25);
    const d = Math.floor(365.25 * c);
    const e = floordiv(b - d, 30.6001);
    t_day = b - d - Math.floor(30.6001 * e);
    t_month = (e < 14) ? (e - 1) : (e - 13);
    t_year = (t_month > 2) ? (c - 4716) : (c - 4715);
    if (year < 0 && t_year <= 0) t_year -= 1;

    const total_mins = hour * 60 + minute + total_delta;
    t_hour = floordiv(pymod(total_mins, 1440), 60);
    t_min = Math.floor(pymod(total_mins, 60));
  }

  // 绝对 UTC 儒略日 = 输入日历（当地）JD - 时区偏移 / 天
  const utc_jd = date_to_julian_day(year, month, day, hour, minute) - (time_type === 1 ? offset_min / 1440.0 : 0);
  // 真太阳时对应的绝对儒略日（用于节气比较与日柱）
  const solar_ut_jd = utc_jd + ((time_type === 1 ? (longitude * 4 + eot_min) : 0)) / 1440.0;

  // 日柱：以真太阳时刻换日（子时归次日的争议此处沿用"午夜换日"口径，与旧版一致）
  const jd = date_to_julian_day(t_year, t_month, t_day, t_hour, t_min);
  const day_ganzhi_idx = pymod(Math.floor(jd + 0.5 + 49), 60);
  const day_tg = TIANGAN[day_ganzhi_idx % 10];
  const day_dz = DIZHI[day_ganzhi_idx % 12];

  // —— 年柱：立春换年（节气为绝对时刻，须与出生绝对 UTC 时刻比较）——
  const cal_year = t_year;
  const li_chun_this = solarTermUtJd(cal_year, 0);
  const bz_year = (utc_jd < li_chun_this) ? (cal_year - 1) : cal_year;
  const y_idx = (bz_year > 0) ? pymod(bz_year - 4, 60) : pymod(bz_year - 3, 60);
  const year_tg = TIANGAN[y_idx % 10], year_dz = DIZHI[y_idx % 12];

  // —— 月柱：以节定月（寅月=立春起，丑月止于次年立春）——
  const year_gan_idx = pymod(bz_year > 0 ? bz_year - 4 : bz_year - 3, 10);
  const base = pymod(year_gan_idx * 2 + 2, 10);   // 五虎遁首月天干
  const starts = [];
  for (let k = 0; k < 11; k++) starts.push(solarTermUtJd(bz_year, 2 * k)); // 立春..大雪
  starts.push(solarTermUtJd(bz_year + 1, 22));                              // 小寒(次年)
  let month_idx = 0;
  for (let k = 1; k < 12; k++) {
    if (utc_jd >= starts[k]) month_idx = k; else break;
  }
  const month_tg = TIANGAN[pymod(base + month_idx, 10)];
  const month_dz = DIZHI[pymod(2 + month_idx, 12)];

  // —— 时柱（真太阳时读数，23:00 起为早子时归次日）——
  const shifted_minutes = pymod(t_hour * 60 + t_min + 60, 1440);
  const hour_dz_idx = floordiv(shifted_minutes, 120);
  const hour_dz = DIZHI[hour_dz_idx];
  const hour_tg = TIANGAN[pymod(pymod(TIANGAN.indexOf(day_tg), 5) * 2 + hour_dz_idx, 10)];

  const ri_zhu = day_tg;

  return {
    t_year, t_month, t_day, t_hour, t_min, jd, utc_jd, solar_ut_jd,
    year_tg, year_dz, month_tg, month_dz, day_tg, day_dz, hour_tg, hour_dz,
    ri_zhu, original_year: year, longitude, timezone,
    offset_min, eot_min, bz_year
  };
}

/* ---------------- 7. 解译报告（含藏干、身强弱、喜用神） ---------------- */
const ELEMENT_ORDER = ["木","火","土","金","水"];

/* —— 8. 大运 / 流年 ——
 * 起运岁数与排运方向：
 *   ctxgender: 'male'|'female'
 *   年干阳 → 男顺女逆；年干阴 → 男逆女顺。
 *   起运：顺排取出生时刻之后最近一个"节"，逆排取之前最近一个"节"，
 *        间隔天数 ÷3 折算起运年（1 天 = 4 个月）。
 *   "节"取节气序号中的双数索引（0 立春、2 惊蛰、4 清明 …… 22 小寒）。
 */

/* JD → 公历日期（格列历，格） */
function jdToDate(jd) {
  const z = Math.floor(jd + 0.5);
  let a;
  if (z < 2299161) a = z;
  else {
    const alpha = floordiv(z - 1867216.25, 36524.25);
    a = z + 1 + alpha - floordiv(alpha, 4);
  }
  const b = a + 1524;
  const c = floordiv(b - 122.1, 365.25);
  const d = Math.floor(365.25 * c);
  const e = floordiv(b - d, 30.6001);
  const day = b - d - Math.floor(30.6001 * e);
  const month = (e < 14) ? e - 1 : e - 13;
  let year = (month > 2) ? c - 4716 : c - 4715;
  if (year <= 0) year -= 1;
  return { year, month, day };
}

/* 附近 5 年内较大范围的"节"查找 */
function nearestSolarTermJd(birth_jd, dir, bz_year) {
  // dir: 1 → 找出生点之后最近的节；-1 → 之前最近的节
  // 覆盖出生年前后若干年，保证能找到
  for (let yr = bz_year - 2; yr <= bz_year + 2; yr++) {
    for (let i = 0; i < 24; i += 2) {          // 只取"节"（索引 0,2,4,...22）
      const term = solarTermUtJd(yr, i);
      const gap = term - birth_jd;
      if (dir === 1 && gap > 1e-4) return term;
      if (dir === -1 && gap < -1e-4) return term;
    }
  }
  return null;
}

function computeDayunAndLiuNian(result, bz_report, gender) {
  const { year_tg, month_tg, month_dz, bz_year, utc_jd } = result;
  const year_gan_yang = YIN_YANG[year_tg] === "阳";   // 年干阴阳
  const is_male = gender === "male";
  // 阳年男 / 阴年女 → 顺排；阴年男 / 阳年女 → 逆排
  const forward = (year_gan_yang === is_male);

  const start = nearestSolarTermJd(utc_jd, forward ? 1 : -1, bz_year);
  let qi_yun_age = 0, qi_yun_days = 0, qi_yun_year = bz_year, qi_yun_date = "";
  if (start != null) {
    // 出生在节之后到下一个节之间的天数 / 前一个节到出生之间的天数
    let span;
    if (forward) span = start - utc_jd;
    else {
      const prev = nearestSolarTermJd(utc_jd, -1, bz_year);
      span = prev != null ? utc_jd - prev : 0;
    }
    qi_yun_days = span;
    // 3 天 = 1 年；余数 1 天 = 4 个月；1/6 天 ≈ 1 年（以小时计）
    const total_days = span;
    qi_yun_age = total_days / 3.0;
    qi_yun_year = bz_year + Math.floor(qi_yun_age);
    // 精确起运公历日期（无闰余近似）
    const qiJd = utc_jd + span * (forward ? 1 : 1);
    const d = jdToDate(forward ? start : (nearestSolarTermJd(utc_jd, -1, bz_year) || start));
    qi_yun_date = `${d.year}-${String(d.month).padStart(2,"0")}-${String(d.day).padStart(2,"0")}`;
  }

  // 从月柱起排大运：顺排 → +1 推进；逆排 → -1
  const idx_tg = TIANGAN.indexOf(month_tg);
  const idx_dz = DIZHI.indexOf(month_dz);
  const step = forward ? 1 : -1;
  const dayun = [];
  let startAge = Math.floor(qi_yun_age < 0 ? 0 : qi_yun_age);
  // 喜用神方向 → 该步大运吉凶
  const yong = (bz_report && bz_report.yong_shen) || "";
  const xi = [];
  if (yong.indexOf("官杀") >= 0) xi.push("正官", "七杀");
  if (yong.indexOf("食伤") >= 0) xi.push("食神", "伤官");
  if (yong.indexOf("财") >= 0) xi.push("正财", "偏财");
  if (yong.indexOf("印") >= 0) xi.push("正印", "偏印");
  if (yong.indexOf("比劫") >= 0) xi.push("比肩", "劫财");
  const ji = [];
  if (yong.indexOf("克泄耗") >= 0) ji.push("正印", "偏印", "比肩", "劫财");
  if (yong.indexOf("生扶") >= 0) ji.push("正官", "七杀", "食神", "伤官", "正财", "偏财");
  for (let k = 0; k < 8; k++) {
    const tg = TIANGAN[pymod(idx_tg + step * (k + 1), 10)];
    const dz = DIZHI[pymod(idx_dz + step * (k + 1), 12)];
    const from = startAge + k * 10;
    const to = from + 9;
    const ss = get_shishen_relation(result.ri_zhu, tg);
    let luck = "平", advice = "此运平稳过渡，宜守成蓄力，静待时机。";
    if (xi.includes(ss)) { luck = "吉"; advice = "此运得喜用神之力，顺势而为可事半功倍，宜大胆进取、把握机遇。"; }
    else if (ji.includes(ss)) { luck = "凶"; advice = "此运逢忌神当道，宜低调守成、稳中求进，避免冒进与重大决策。"; }
    dayun.push({ gan: tg, zhi: dz, from, to, shishen: ss, luck, advice });
  }

  return { qi_yun_age, qi_yun_days, qi_yun_date, dayun, forward };
}

/* 判断某十神是否属于喜用神 */
function isYongShen(ss, yong) {
  if (!yong) return false;
  if (yong.indexOf("官杀") >= 0 && (ss === "正官" || ss === "七杀")) return true;
  if (yong.indexOf("食伤") >= 0 && (ss === "食神" || ss === "伤官")) return true;
  if (yong.indexOf("财") >= 0 && (ss === "正财" || ss === "偏财")) return true;
  if (yong.indexOf("印") >= 0 && (ss === "正印" || ss === "偏印")) return true;
  if (yong.indexOf("比劫") >= 0 && (ss === "比肩" || ss === "劫财")) return true;
  return false;
}

/* 婚姻与事业分析
 * 婚姻：男命以正财为妻、偏财为偏缘；女命以正官为夫、七杀为偏缘。
 *       日支为婚姻宫，看配偶星旺衰、婚姻宫是否被冲、配偶星是否喜用。
 * 事业：统计命局官杀/财/食伤/印/比劫五组十神力量，取最强者为事业主导星，
 *       结合格局与喜用神给出事业类型与建议。
 */
function computeMarriageAndCareer(result, report, gender) {
  const ri_zhu = result.ri_zhu;
  const is_male = gender === "male";
  const spouseMain = is_male ? "正财" : "正官";
  const spouseSide = is_male ? "偏财" : "七杀";
  const spouseStars = [spouseMain, spouseSide];

  // 统计命局十神分布（天干 + 地支藏干）
  const stems = [result.year_tg, result.month_tg, result.hour_tg];
  const branches = [result.year_dz, result.month_dz, result.day_dz, result.hour_dz];
  const counts = { "比肩":0,"劫财":0,"正印":0,"偏印":0,"食神":0,"伤官":0,"正官":0,"七杀":0,"正财":0,"偏财":0 };
  let spouseCount = 0, spouseInStem = 0;
  stems.forEach(s => {
    const ss = get_shishen_relation(ri_zhu, s);
    counts[ss]++;
    if (spouseStars.includes(ss)) { spouseCount++; spouseInStem++; }
  });
  branches.forEach(bz => {
    HIDDEN_STEMS[bz].forEach(s => {
      const ss = get_shishen_relation(ri_zhu, s);
      counts[ss]++;
      if (spouseStars.includes(ss)) spouseCount++;
    });
  });

  // 婚姻宫 = 日支；是否被其他地支相冲
  const palace = result.day_dz;
  const palaceRelation = get_shishen_relation(ri_zhu, primaryHiddenStem(palace));
  const CHONG = { "子":"午","午":"子","丑":"未","未":"丑","寅":"申","申":"寅","卯":"酉","酉":"卯","辰":"戌","戌":"辰","巳":"亥","亥":"巳" };
  const chonged = branches.some(bz => bz === CHONG[palace]);
  const yong = (report && report.yong_shen) || "";
  const spouseIsYong = isYongShen(spouseMain, yong) || isYongShen(spouseSide, yong);

  // 婚姻结论
  let spouseFate, palaceTxt, spouseHelp;
  if (spouseCount >= 3) spouseFate = `配偶星（${spouseMain}）在命局中出现 ${spouseCount} 处，力量较旺，异性缘分相对较多，感情经历可能较为丰富。此为缘分数量描述，不代表忠诚度或出轨倾向，亦不预示婚恋必然顺利，关键仍在双方用心经营。`;
  else if (spouseCount === 2) spouseFate = `配偶星（${spouseMain}）出现 ${spouseCount} 处，力量适中，婚恋缘分正常，宜在适龄阶段主动把握良缘。`;
  else if (spouseCount === 1) spouseFate = `配偶星（${spouseMain}）仅出现 ${spouseCount} 处，力量偏弱，婚恋缘分相对平淡，宜扩大社交圈、主动争取，晚婚更利。`;
  else spouseFate = `配偶星（${spouseMain}）在命局中不显，婚恋缘分来得较晚，宜晚婚，婚后感情需用心经营。`;

  if (chonged) palaceTxt = `婚姻宫（日支${palace}）被其他地支相冲，感情易有波折与变动，婚后需多包容、多沟通，避免意气用事。`;
  else if (spouseStars.includes(palaceRelation)) palaceTxt = `婚姻宫（日支${palace}）坐${palaceRelation}，为配偶星入宫，夫妻感情深厚，婚姻基础稳固。`;
  else palaceTxt = `婚姻宫（日支${palace}）安稳无冲，婚姻基础稳固，感情发展平顺。`;

  if (spouseIsYong) spouseHelp = `配偶星为命局喜用神，婚后得配偶助力，夫妻同心则家业兴旺。`;
  else spouseHelp = `配偶星为命局忌神，婚后需注意磨合，多体谅对方，共同经营方能长久。`;

  // 事业分析：五组十神力量
  const group = {
    "官杀": counts["正官"] + counts["七杀"],
    "财": counts["正财"] + counts["偏财"],
    "食伤": counts["食神"] + counts["伤官"],
    "印": counts["正印"] + counts["偏印"],
    "比劫": counts["比肩"] + counts["劫财"]
  };
  const sorted = Object.keys(group).sort((a, b) => group[b] - group[a]);
  const main = sorted[0];
  const mainCount = group[main];

  // 五行→现代行业（第 1 层：行业方向，参考主流"最旺五行定行业"）
  const ELEMENT_INDUSTRY = {
    "木": { dir: "成长、教育与生命力", inds: ["教育", "出版", "媒体", "时尚", "家具", "中医药", "环保", "健康养生", "文化文创", "产品设计"] },
    "火": { dir: "能源、曝光与传播转化", inds: ["科技电子", "互联网软件", "演艺娱乐", "能源", "广告公关", "市场营销", "美容美发", "摄影传媒", "新媒体运营"] },
    "土": { dir: "稳定、资源与项目管理", inds: ["房地产", "建筑施工", "土木工程", "矿业陶瓷", "保险", "人力资源", "农牧", "仓储物流", "咨询顾问", "项目管理"] },
    "金": { dir: "精准、结构与价值计量", inds: ["金融银行", "证券投资", "法律司法", "军警安保", "汽车机械", "五金制造", "珠宝钟表", "外科牙科", "精密工程", "硬件科技"] },
    "水": { dir: "流动、沟通与智慧", inds: ["贸易进出口", "物流运输", "航运港口", "旅游观光", "餐饮", "新闻", "研究科研", "国际贸易", "咨询顾问", "AI/大数据"] }
  };
  // 十神→现代行业/岗位（第 2 层：角色工种）
  const SHISHEN_INDUSTRY = {
    "官杀": { inds: ["企业管理", "政府公职", "法务合规", "执法", "危机公关", "项目管理", "行政管理"] },
    "财":   { inds: ["经商创业", "金融投融资", "销售", "财务", "贸易", "市场商务"] },
    "食伤": { inds: ["产品", "设计", "研发", "内容创作", "自媒体", "演艺", "咨询", "授课", "写作"] },
    "印":   { inds: ["教育", "科研", "文化", "医疗", "学术", "出版", "顾问", "心理咨询"] },
    "比劫": { inds: ["独立创业", "销售", "竞技", "自由职业", "合伙经营"] }
  };

  // 最旺五行 / 最缺五行（加权能量）
  const powerEl = (report && report.elements_power) ? report.elements_power : null;
  let topEl = "", leastEl = "";
  if (powerEl) {
    let bv = -1, wv = 1e9;
    ["木", "火", "土", "金", "水"].forEach(w => {
      const v = powerEl[w] || 0;
      if (v > bv) { bv = v; topEl = w; }
      if (v < wv) { wv = v; leastEl = w; }
    });
  }

  let careerType, careerAnalysis, careerAdvice;
  switch (main) {
    case "官杀":
      careerType = "管理权力型";
      careerAnalysis = `命局官杀星最旺（${mainCount} 处），事业心强、有领导欲与责任感，适合体制内、企业管理、执法等需要权威与规则的领域。`;
      careerAdvice = `官星喜印相生则权柄稳固，宜走稳健晋升路线；若身弱官杀过旺，需以印化杀、以食制杀，避免压力过大。`;
      break;
    case "财":
      careerType = "财富经营型";
      careerAnalysis = `命局财星最旺（${mainCount} 处），商业嗅觉敏锐、务实重利，适合经商、金融、贸易等财富积累型领域。`;
      careerAdvice = `身强财旺则富贵可期，宜大胆开拓；身弱财多则需以印比生扶，先稳根基再图发展，忌贪多求快。`;
      break;
    case "食伤":
      careerType = "才华技术型";
      careerAnalysis = `命局食伤星最旺（${mainCount} 处），才华横溢、创造力强，适合技术、创意、演艺、自媒体等靠才华变现的领域。`;
      careerAdvice = `食伤生财则才华可源源变现，宜专注打磨核心技能；忌伤官见官，避免锋芒过露招惹是非。`;
      break;
    case "印":
      careerType = "学术文化型";
      careerAnalysis = `命局印星最旺（${mainCount} 处），好学深思、重名誉，适合教育、科研、文化、医疗等靠专业壁垒与声誉立足的领域。`;
      careerAdvice = `印星为用则利学业功名，宜深耕专业、积累口碑；忌印重懒散，需以财制印、以食伤泄秀，保持行动力。`;
      break;
    default:
      careerType = "竞争合伙型";
      careerAnalysis = `命局比劫星最旺（${mainCount} 处），独立自主、竞争意识强，适合创业、销售、竞技等需要个人硬实力的领域。`;
      careerAdvice = `比劫旺者宜独立开拓，合伙需谨慎分利；身弱则喜比劫帮扶，可借团队之力共同发展。`;
  }

  // —— 五行行业 + 喜用/中和 补充（对齐主流"五行定行业、喜用定最顺赛道"的三层结构）——
  const elDir = topEl && ELEMENT_INDUSTRY[topEl] ? ELEMENT_INDUSTRY[topEl] : null;
  const shiInds = SHISHEN_INDUSTRY[main] ? SHISHEN_INDUSTRY[main].inds : [];
  const ratioEl = (report && report.strength) ? report.strength.ratio : null;
  const isNeutral = ratioEl != null && ratioEl > 0.45 && ratioEl < 0.55;
  const elNote = elDir
    ? `命局${topEl}气偏盛、主“${elDir.dir}”。就行业方向看，较契合的现代行业有：${elDir.inds.join("、")}。`
    : "";
  const shiNote = shiInds.length
    ? `命局十神以“${main}”最旺，职业角色倾向：${shiInds.join("、")}。`
    : "";
  const yongNote = isNeutral
    ? "命局中和、喜用方向不分明，且不判唯一定论，行业取舍以上面的五行/十神倾向作参考即可。"
    : ((report && report.yong_shen) ? `喜用方向为「${report.yong_shen}」，往喜用对应的行业走更容易发挥自身优势。` : "");
  if (elNote) careerAnalysis = careerAnalysis + " " + elNote;
  if (yongNote) careerAdvice = careerAdvice + " " + yongNote;

  return {
    marriage: { spouseMain, spouseSide, spouseCount, spouseInStem, palace, palaceRelation, chonged, spouseIsYong, spouseFate, palaceTxt, spouseHelp },
    career: { main, mainCount, careerType, careerAnalysis, careerAdvice, monthRelation: report ? report.month_relation : "",
      element: topEl, elementDir: elNote, roleDir: shiNote, yongNote,
      elementIndustries: elDir ? elDir.inds : [], roleIndustries: shiInds }
  };
}

/* 流年干支：以立春换年（与年柱口径一致） */
function liunianGanzhi(birth_info, year) {
  // 流年干支由该公历年的立春决定，与出生时刻无关；直接以 year 作为干支基准年，
  // 避免误用出生时刻去比未来流年立春而导致整体错位一年。
  void birth_info; // 保留参数以兼容既有调用方，当前实现不再依赖出生时刻
  const bz = year;
  const y_idx = (bz > 0) ? pymod(bz - 4, 60) : pymod(bz - 3, 60);
  return { gan: TIANGAN[y_idx % 10], zhi: DIZHI[y_idx % 12], year, bz };
}

/* 生我者（印的五行） */
function parentElementOf(me_x) {
  return ELEMENT_ORDER[pymod(ELEMENT_ORDER.indexOf(me_x) - 1, 5)];
}

/* 加权身强弱评分 */
function evaluateStrength(ri_zhu, stems, branches, month_dz) {
  const me_x = WU_XING[ri_zhu];
  const parent_x = parentElementOf(me_x);
  const is_ally = wx => (wx === me_x || wx === parent_x);

  const power = { "木":0, "火":0, "土":0, "金":0, "水":0 };
  let ally = 0, foe = 0;

  // 天干：每个记 100
  for (const s of stems) {
    const w = 100;
    power[WU_XING[s]] += w;
    if (is_ally(WU_XING[s])) ally += w; else foe += w;
  }
  // 地支：藏干按本/中/余气加权，月令(月支)整体 ×1.6（得令）
  branches.forEach((bz, i) => {
    const hidden = HIDDEN_STEMS[bz];
    const mf = (bz === month_dz) ? 1.6 : 1.0;
    hidden.forEach((stem, k) => {
      const w = (hidden.length === 1) ? 100 : (HIDDEN_WEIGHT[k] || 0);
      const v = w * mf;
      power[WU_XING[stem]] += v;
      if (is_ally(WU_XING[stem])) ally += v; else foe += v;
    });
  });

  const total = ally + foe;
  const ratio = total > 0 ? ally / total : 0.5;
  let label;
  if (ratio >= 0.62) label = "身强 · 能量充盈";
  else if (ratio >= 0.55) label = "身偏强";
  else if (ratio <= 0.38) label = "身弱 · 需借力发展";
  else if (ratio <= 0.45) label = "身偏弱";
  else label = "中和";

  // 喜用神方向
  let yong;
  if (ratio >= 0.55) yong = "克泄耗（官杀 / 食伤 / 财）";
  else if (ratio <= 0.45) yong = "生扶（正偏印 / 比劫）";
  else yong = "五行流通（顺势而为）";

  return { power, ally, foe, ratio, label, yong };
}

function generate_report(result) {
  const { ri_zhu, year_tg, year_dz, month_tg, month_dz, day_dz, hour_tg, hour_dz } = result;
  const me_x = WU_XING[ri_zhu];

  // 月令格局：以月支本气天干论十神
  const month_primary = primaryHiddenStem(month_dz);
  const month_relation = get_shishen_relation(ri_zhu, month_primary);

  const all_symbols = [year_tg, year_dz, month_tg, month_dz, ri_zhu, day_dz, hour_tg, hour_dz];
  const elements_count = { "木":0, "火":0, "土":0, "金":0, "水":0 };
  all_symbols.forEach(sym => { elements_count[WU_XING[sym]] += 1; });

  const stems = [year_tg, month_tg, ri_zhu, hour_tg];
  const branches = [year_dz, month_dz, day_dz, hour_dz];
  const strength = evaluateStrength(ri_zhu, stems, branches, month_dz);

  // 藏干明细（供前端展示）
  const hidden_stems = {
    "年": { "支": year_dz, "藏干": HIDDEN_STEMS[year_dz] },
    "月": { "支": month_dz, "藏干": HIDDEN_STEMS[month_dz] },
    "日": { "支": day_dz, "藏干": HIDDEN_STEMS[day_dz] },
    "时": { "支": hour_dz, "藏干": HIDDEN_STEMS[hour_dz] }
  };

  // 十神总览（相对日主）
  const shishen = {
    "年干": get_shishen_relation(ri_zhu, year_tg),
    "月干": get_shishen_relation(ri_zhu, month_tg),
    "日主": "元男/元女",
    "时干": get_shishen_relation(ri_zhu, hour_tg),
    "月令": month_relation
  };

  const detail = PATTERN_DETAILS[month_relation] || FALLBACK_DETAIL;
  const parent_element = parentElementOf(me_x);

  // 四柱逐柱解读（宫位 + 干支 + 十神）
  const pillars_detail = {
    "年柱": { "干支": year_tg + year_dz, "十神": get_shishen_relation(ri_zhu, year_tg), "宫位": PILLAR_MEANING["年柱"]["宫位"], "说明": PILLAR_MEANING["年柱"]["说明"] },
    "月柱": { "干支": month_tg + month_dz, "十神": month_relation, "宫位": PILLAR_MEANING["月柱"]["宫位"], "说明": PILLAR_MEANING["月柱"]["说明"] },
    "日柱": { "干支": ri_zhu + day_dz, "十神": "日主（自身）", "宫位": PILLAR_MEANING["日柱"]["宫位"], "说明": PILLAR_MEANING["日柱"]["说明"] },
    "时柱": { "干支": hour_tg + hour_dz, "十神": get_shishen_relation(ri_zhu, hour_tg), "宫位": PILLAR_MEANING["时柱"]["宫位"], "说明": PILLAR_MEANING["时柱"]["说明"] }
  };

  return {
    me_x, month_relation, elements_count, elements_power: strength.power,
    parent_element, strength, hidden_stems, shishen,
    power_status: strength.label, yong_shen: strength.yong,
    detail, pillars_detail
  };
}

/* 十神 → 相对日主的十神大类（用于五行能量详解·旺衰解读，动态、不写死） */
const SHISHEN_GROUP = {
  "比肩": "同我者（比劫）", "劫财": "同我者（比劫）",
  "正印": "生我者（印）",   "偏印": "生我者（印）",
  "食神": "我生者（食伤）", "伤官": "我生者（食伤）",
  "正官": "克我者（官杀）", "七杀": "克我者（官杀）",
  "正财": "我克者（财）",   "偏财": "我克者（财）"
};

/* 返回 木/火/土/金/水 → 相对日主 me_x 的十神大类（随日主变化，动态正确） */
function elementShishenGroup(me_x) {
  const rep = { "木": "甲", "火": "丙", "土": "戊", "金": "庚", "水": "壬" };
  const out = {};
  for (const wx of ELEMENT_ORDER) {
    out[wx] = SHISHEN_GROUP[get_shishen_relation(rep[me_x], rep[wx])];
  }
  return out;
}

/* =====================================================================
 * 9. 八字合婚（学习演示，仅供娱乐与研究，不构成任何婚恋建议）
 * ---------------------------------------------------------------------
 * 基于双方四柱的客观可计算指标综合评分，六个维度（合计 100 分）：
 *   ① 年支（生肖）合冲      —— 占比 10 分（网上主流权重下生肖占比最低，故降权）
 *   ② 日干（日主）五合生克  —— 占比 25 分（合婚最重日主）
 *   ③ 日支（婚姻宫）合冲    —— 占比 20 分
 *   ④ 五行能量互补度        —— 占比 15 分
 *   ⑤ 喜用神互补度          —— 占比 20 分
 *   ⑥ 格局阴阳（纯阳/纯阴） —— 占比 10 分
 * 说明：合婚为传统民俗文化内容，无科学依据，评分仅供娱乐参考。
 * ===================================================================== */

/* 地支关系映射（双向） */
const HE_COMBINE  = { "子":"丑","丑":"子","寅":"亥","亥":"寅","卯":"戌","戌":"卯","辰":"酉","酉":"辰","巳":"申","申":"巳","午":"未","未":"午" };   // 六合
const HE_SANHE    = { "申":"子辰","子":"申辰","辰":"申子","寅":"午戌","午":"寅戌","戌":"寅午","巳":"酉丑","酉":"巳丑","丑":"巳酉","亥":"卯未","卯":"亥未","未":"亥卯" }; // 三合
const HE_CLASH    = { "子":"午","午":"子","丑":"未","未":"丑","寅":"申","申":"寅","卯":"酉","酉":"卯","辰":"戌","戌":"辰","巳":"亥","亥":"巳" };   // 六冲
const HE_HARM     = { "子":"未","未":"子","丑":"午","午":"丑","寅":"巳","巳":"寅","卯":"辰","辰":"卯","申":"亥","亥":"申","酉":"戌","戌":"酉" };   // 六害
const HE_PUNISH   = { "寅":"巳","巳":"申","申":"寅","丑":"戌","戌":"未","未":"丑","子":"卯","卯":"子","辰":"辰","午":"午","酉":"酉","亥":"亥" };   // 相刑（含自刑）

/* 十二地支对应生肖（动物名），供合婚文案通俗化显示 */
const ZODIAC = { "子":"鼠","丑":"牛","寅":"虎","卯":"兔","辰":"龙","巳":"蛇","午":"马","未":"羊","申":"猴","酉":"鸡","戌":"狗","亥":"猪" };

/* 五行生克（单向） */
const HE_SHENG = { "木":"火", "火":"土", "土":"金", "金":"水", "水":"木" };  // 我生
const HE_KE    = { "木":"土", "火":"金", "土":"水", "金":"木", "水":"火" };  // 我克

/* 天干五合（甲己合土、乙庚合金、丙辛合水、丁壬合木、戊癸合火），双向映射 */
const HE_TIANGAN_HE = { "甲":"己","己":"甲","乙":"庚","庚":"乙","丙":"辛","辛":"丙","丁":"壬","壬":"丁","戊":"癸","癸":"戊" };

/* 返回两支关系（a 相对 b），供生肖与婚姻宫共同使用 */
function branchRelationHe(a, b) {
  if (HE_COMBINE[a] === b) return { type: "liuhe",  label: "六合", good: true,  strong: true,  text: `${a}${b}为六合` };
  if (HE_SANHE[a] && HE_SANHE[a].includes(b)) return { type: "sanhe", label: "三合", good: true, strong: false, text: `${a}${b}为三合` };
  if (HE_CLASH[a] === b) return { type: "clash",  label: "六冲", good: false, strong: true,  text: `${a}${b}为六冲` };
  if (HE_HARM[a] === b)  return { type: "harm",   label: "六害", good: false, strong: false, text: `${a}${b}为相害` };
  if (HE_PUNISH[a] === b || HE_PUNISH[b] === a) return { type: "punish", label: "相刑", good: false, strong: false, text: `${a}${b}为相刑` };
  return { type: "normal", label: "平和", good: null, strong: false, text: `${a}${b}无冲合` };
}

/* 返回两五行生克关系 */
function wuxingRelationHe(xa, xb) {
  if (xa === xb) return { type: "same", label: "比和", text: `${xa}${xb}同类` };
  if (HE_SHENG[xa] === xb) return { type: "sheng", label: "相生", text: `${xa}生${xb}` };
  if (HE_SHENG[xb] === xa) return { type: "sheng", label: "相生", text: `${xb}生${xa}` };
  if (HE_KE[xa] === xb) return { type: "ke", label: "相克", text: `${xa}克${xb}` };
  if (HE_KE[xb] === xa) return { type: "ke", label: "相克", text: `${xb}克${xa}` };
  return { type: "normal", label: "平和", text: `${xa}${xb}` };
}

/* 返回某个命局的喜用（所需）五行集合 */
function yongWuxings(me_x, ratio) {
  if (ratio >= 0.55) {
    // 身强：喜克泄耗 = 克我（官杀）、我生（食伤）、我克（财）
    const keWo = ELEMENT_ORDER.find(w => HE_KE[w] === me_x);   // 克我者
    const woSheng = HE_SHENG[me_x];                            // 我生者
    const woKe = HE_KE[me_x];                                  // 我克者
    return [keWo, woSheng, woKe];
  }
  if (ratio <= 0.45) {
    // 身弱：喜生扶 = 生我（印）、同我（比劫）
    const shengWo = parentElementOf(me_x);
    return [shengWo, me_x];
  }
  return ELEMENT_ORDER.slice(); // 中和：喜流通
}

/* 返回命局最旺的两个五行（按加权能量降序） */
function topWuxings(power) {
  return ELEMENT_ORDER.slice().sort((a, b) => (power[b] || 0) - (power[a] || 0)).slice(0, 2);
}

/* ---------- 合婚详细解析文案生成 ---------- */

/* 生肖 / 婚姻宫（地支）关系的白话解析 */
function hehunZhiText(rel, a, b, scope) {
  switch (rel.type) {
    case "liuhe":  return `${scope}「${a}」与「${b}」为六合，地支相合中较吉利的一类，彼此性情相投、互相吸引，相处轻松愉悦，感情根基稳定。`;
    case "sanhe":  return `${scope}「${a}」与「${b}」为三合，彼此呼应、志趣相近，配合默契，能互相成就、共同进步。`;
    case "clash":  return `${scope}「${a}」与「${b}」为六冲，正面相冲，性格与节奏差异较大，容易起争执、闹矛盾，需要双方多磨合、多忍让。`;
    case "harm":   return `${scope}「${a}」与「${b}」为相害，暗中相妨，表面平静、内里易生隔阂，需坦诚沟通、及时化解误会。`;
    case "punish": return `${scope}「${a}」与「${b}」为相刑，长期相处易有摩擦与内耗，需彼此包容、少较真。`;
    default:       return `${scope}「${a}」与「${b}」不冲不合，关系平和，虽无大吉大利，也没有明显冲克，顺其自然即可。`;
  }
}

/* 日主五行生克的白话解析 */
function hehunWuxingText(rel, zdx, ydx) {
  switch (rel.type) {
    case "sheng": return `甲方日主属${zdx}、乙方日主属${ydx}，${rel.text}，五行相生，一方能滋养另一方，付出与回馈形成良性循环，相处舒适融洽。`;
    case "same":  return `双方日主同属${zdx}，五行比和，志趣相投、心有灵犀、默契十足；但同类相叠也可能固执己见，稍缺一点互补调剂。`;
    case "ke":    return `甲方日主属${zdx}、乙方日主属${ydx}，${rel.text}，五行相克，相处中一方偏强势、一方易有压力，需把握主导分寸、互相尊重。`;
    default:      return `双方日主五行平和，无明显的生克牵制，关系独立又和缓。`;
  }
}

/* 五行能量互补度的白话解析 */
function hehunHubuText(hubu, topA, topB) {
  let s = `甲方最旺五行为「${topA.join("、")}」，乙方最旺五行为「${topB.join("、")}」。`;
  if (hubu.identical) s += `双方五行分布完全一致、强弱趋同，亲和有余而同气过旺，缺少互补差异，需主动创造新鲜感与各自空间。`;
  else if (hubu.complement >= 2) s += `双方五行强弱明显错位、彼此补足（互补 ${hubu.complement} 项），能各取所长、互相扶持，是相当理想的搭配。`;
  else if (hubu.complement === 1) s += `双方有 ${hubu.complement} 项五行互补，能起到一定的取长补短效果。`;
  else if (hubu.overlap >= 2) s += `双方五行缺少互补，偏强的部分重叠（${hubu.overlap} 项同类趋同），性情相似但易各执己见，需互相包容理解。`;
  else s += `双方五行缺少互补，各自偏强的部分重叠，容易出现争夺或互相不理解。`;
  return s;
}

/* 喜用神互补度的白话解析 */
function hehunYongText(dimY, topA, topB) {
  const a = dimY.aFoxiangB, b = dimY.bFoxiangA;
  if (dimY.neutral) {
    const base = (a && b) ? "本来喜用互旺" : (a || b) ? "本来存在单向补益" : "本无补益";
    return `一方或双方命局为「中和」，喜用方向不明确，此维度按保守口径降档计分（${base}），避免虚高。`;
  }
  if (a && b) return `甲方最旺的「${topA[0]}」恰是乙方命局所需，乙方最旺的「${topB[0]}」也恰是甲方所需，双方喜用神互相成就，是合婚中难得的「互相旺对方」组合。`;
  if (a) return `甲方最旺的「${topA[0]}」正是乙方命局所缺所需，甲能补乙，能给对方带来实质助力。`;
  if (b) return `乙方最旺的「${topB[0]}」正是甲方命局所缺所需，乙能补甲，能给对方带来实质助力。`;
  return `双方喜用神互补较弱，各自的强势之处并非对方所需，难以形成「补益」效应。`;
}

/* 合婚主函数：入参为双方的 execute 结果 + generate_report 结果 */
/* 判断命局是否为四柱纯阳 / 纯阴（四天干四地支阴阳一致） */
function detectPureYinYang(result) {
  const stems = [result.year_tg, result.month_tg, result.day_tg, result.hour_tg];
  const branches = [result.year_dz, result.month_dz, result.day_dz, result.hour_dz];
  const allYang = stems.every(t => YIN_YANG[t] === "阳") && branches.every(b => YIN_YANG[b] === "阳");
  const allYin  = stems.every(t => YIN_YANG[t] === "阴") && branches.every(b => YIN_YANG[b] === "阴");
  if (allYang) return "纯阳";
  if (allYin) return "纯阴";
  return "非纯";
}

/* 天干五合（有情之合）的白话解析 */
function hehunWuheText(rel, tgA, tgB) {
  return `甲方日干「${tgA}」与乙方日干「${tgB}」为天干五合，属「有情之合」，彼此情投意合、吸引力强，是日主层面恩爱的象征，感情根基深厚。`;
}

function computeHehun(resA, repA, resB, repB) {
  const zdx = repA.me_x;               // 甲方日主五行
  const ydx = repB.me_x;               // 乙方日主五行
  const tgA = resA.day_tg, tgB = resB.day_tg;  // 双方日干（天干五合判定用）
  const zxz = resA.year_dz;            // 甲方生肖（年支）
  const yxz = resB.year_dz;            // 乙方生肖
  const zhdz = resA.day_dz;            // 甲方婚姻宫（日支）
  const yhdz = resB.day_dz;            // 乙方婚姻宫

  // —— ① 生肖（年支）满分 10（网上主流权重下生肖占比最低，故降权）——
  const sxRel = branchRelationHe(zxz, yxz);
  const sxScore = sxRel.type === "liuhe" ? 10 : sxRel.type === "sanhe" ? 8 : sxRel.type === "normal" ? 6 : sxRel.type === "clash" ? 0 : 3;

  // —— ② 日主（日干）：先判天干五合（有情之合），再判五行生克，满分 25（合婚最重日主）——
  let rgRel, rgScore;
  if (HE_TIANGAN_HE[tgA] === tgB) {
    rgRel = { type: "he", label: "天干相合", good: true, strong: true, text: `${tgA}${tgB}为天干五合，有情之合` };
    rgScore = 25;
  } else {
    rgRel = wuxingRelationHe(zdx, ydx);
    rgScore = rgRel.type === "sheng" ? 20 : rgRel.type === "same" ? 15 : 6;
  }

  // —— ③ 日支（婚姻宫）满分 20 ——
  const hgRel = branchRelationHe(zhdz, yhdz);
  const hgScore = hgRel.type === "liuhe" ? 20 : hgRel.type === "sanhe" ? 16 : hgRel.type === "normal" ? 12 : hgRel.type === "clash" ? 3 : 7;

  // —— ④ 五行能量互补 ——
  const pa = repA.elements_power, pb = repB.elements_power;
  const suma = ELEMENT_ORDER.reduce((s, w) => s + (pa[w] || 0), 0) || 1;
  const sumb = ELEMENT_ORDER.reduce((s, w) => s + (pb[w] || 0), 0) || 1;
  let complement = 0, overlap = 0;             // overlap = 同类重合（同强或同弱），非冲突
  ELEMENT_ORDER.forEach(w => {
    const da = (pa[w] || 0) / suma, db = (pb[w] || 0) / sumb;
    const deva = da - 0.2, devb = db - 0.2;
    if ((deva > 0.05 && devb < -0.05) || (deva < -0.05 && devb > 0.05)) complement++;
    else if (Math.abs(deva) > 0.05 && Math.abs(devb) > 0.05 && (deva > 0) === (devb > 0)) overlap++;
  });
  let buScore = 8 + complement * 2;                    // 基础 8（网上视"平和/无明显互补"为可接受，不把缺互补当大扣），每补 1 项 +2
  buScore = Math.max(8, Math.min(15, Math.round(buScore)));  // 同类重合仅说明缺互补，下限保 8，不再压到低分

  // —— ⑤ 喜用神互补 ——
  const yongA = yongWuxings(zdx, repA.strength.ratio);
  const yongB = yongWuxings(ydx, repB.strength.ratio);
  const topB = topWuxings(pb), topA = topWuxings(pa);
  const aFoxiangB = yongB.some(w => topA[0] === w);     // 甲最旺 = 乙所需
  const bFoxiangA = yongA.some(w => topB[0] === w);     // 乙最旺 = 甲所需
  const aErxiangB = yongB.some(w => topA[1] === w);
  const bErxiangA = yongA.some(w => topB[1] === w);
  let yongScore;
  if ((aFoxiangB && bFoxiangA)) yongScore = 20;         // 双向强互补
  else if (aFoxiangB || bFoxiangA || (aErxiangB && bErxiangA)) yongScore = 14; // 单向或次强双向
  else if (aErxiangB || bErxiangA) yongScore = 10;
  else yongScore = 6;

  // 中和命局（0.45 < ratio < 0.55）喜用方向不明确，该维度降一档，避免评分虚高
  const neutralA = repA.strength.ratio > 0.45 && repA.strength.ratio < 0.55;
  const neutralB = repB.strength.ratio > 0.45 && repB.strength.ratio < 0.55;
  const neutral = neutralA || neutralB;
  if (neutral) {
    if (yongScore === 20) yongScore = 14;
    else if (yongScore === 14) yongScore = 10;
    else if (yongScore === 10) yongScore = 8;   // 8 为下限，不再因中和压到过低
  }

  // —— ⑥ 格局阴阳（四柱纯阳/纯阴）满分 10 ——
  const pureA = detectPureYinYang(resA), pureB = detectPureYinYang(resB);
  const aPure = pureA !== "非纯", bPure = pureB !== "非纯";
  let gejuScore, gejuText;
  if (aPure && bPure && pureA !== pureB) {
    gejuScore = 10;
    gejuText = `甲方为「${pureA}」、乙方为「${pureB}」，孤阳遇孤阴、刚柔相济，阴阳得以调合，属难得的互补格局。`;
  } else if (pureA === "纯阳" && pureB === "纯阳") {
    gejuScore = 3;
    gejuText = "双方均为纯阳之命，阳气过盛、性格皆偏刚烈强势，易硬碰硬，需以柔克刚、多退让。";
  } else if (pureA === "纯阴" && pureB === "纯阴") {
    gejuScore = 3;
    gejuText = "双方均为纯阴之命，阴气偏重、性格皆内敛敏感，易冷处理、生隔阂，需主动沟通、坦诚交心。";
  } else if (aPure || bPure) {
    gejuScore = 6;
    const pureSide = aPure ? "甲方" : "乙方";
    const pureKind = aPure ? pureA : pureB;
    gejuText = `${pureSide}为「${pureKind}」独特性格格局、另一方为常规格局；纯者偏执一端，需对方以包容调剂，互补中略带磨合。`;
  } else {
    gejuScore = 5;
    gejuText = "双方均为常规格局（非纯阳、非纯阴），阴阳分布平稳，无特殊偏枯之象。";
  }

  const score = sxScore + rgScore + hgScore + buScore + yongScore + gejuScore;
  let level, verdict;
  if (score >= 85) { level = "上等婚"; verdict = "天作之合，双方生肖、日主与婚姻宫高度契合，五行互补，情感根基深厚。"; }
  else if (score >= 70) { level = "中上等婚"; verdict = "良配，契合度较高，只要经营得当，感情生活可和谐美满。"; }
  else if (score >= 55) { level = "中等婚"; verdict = "缘分一般，相处中需多包容磨合，把差异化为互补。"; }
  else if (score >= 40) { level = "中下等婚"; verdict = "契合度偏低，冲克较多，需双方付出更多耐心与理解去经营。"; }
  else { level = "下等婚"; verdict = "冲克较重，感情易生波折，若同居共处需格外用心化解分歧。"; }

  // 四柱完全相同（同一天同一时辰）：同性相求，专门文案，避免被通用档位"冲克"措辞误导
  const identical = resA.year_tg  === resB.year_tg  && resA.year_dz  === resB.year_dz &&
                    resA.month_tg === resB.month_tg && resA.month_dz === resB.month_dz &&
                    resA.day_tg   === resB.day_tg   && resA.day_dz   === resB.day_dz &&
                    resA.hour_tg  === resB.hour_tg  && resA.hour_dz  === resB.hour_dz;
  if (identical) {
    level = "中等婚";
    verdict = "双方八字如出一辙，性情、三观与气场高度同频，天生气机相引，缘分极深、默契十足。但同气过旺而五行缺互补，宛如照镜自怜，易趋同固执、少差异调剂；若能以差异为贵、相互扩容，是可以长久相伴的一对。";
  }

  // —— 详细白话解析 ——
  const analysis = {
    summary: `甲方日主「${resA.ri_zhu}」属${zdx}、生肖${ZODIAC[zxz]}（${zxz}），乙方日主「${resB.ri_zhu}」属${ydx}、生肖${ZODIAC[yxz]}（${yxz}），六维综合 ${score} 分，判为「${level}」。${verdict}`,
    shengxiao: hehunZhiText(sxRel, zxz, yxz, "年支生肖"),
    rigan:    rgRel.type === "he" ? hehunWuheText(rgRel, tgA, tgB) : hehunWuxingText(rgRel, zdx, ydx),
    hunyin:   hehunZhiText(hgRel, zhdz, yhdz, "婚姻宫（日支）"),
    hubu:     hehunHubuText({ complement, overlap, identical }, topA, topB),
    yongshen: hehunYongText({ aFoxiangB, bFoxiangA, neutral }, topA, topB),
    geju:     gejuText
  };

  return {
    score, level, verdict, analysis,
    a: { ri_zhu: resA.ri_zhu, me_x: zdx, year_zhi: zxz, day_zhi: zhdz, power: pa, top: topA, yong: yongA, pure: pureA },
    b: { ri_zhu: resB.ri_zhu, me_x: ydx, year_zhi: yxz, day_zhi: yhdz, power: pb, top: topB, yong: yongB, pure: pureB },
    dims: {
      shengxiao: { score: sxScore, rel: sxRel },
      rigan:    { score: rgScore, rel: rgRel },
      hunyin:   { score: hgScore, rel: hgRel },
      hubu:     { score: buScore, complement, overlap },
      yongshen: { score: yongScore, aFoxiangB, bFoxiangA, neutral },
      geju:     { score: gejuScore, pureA, pureB }
    }
  };
}

/* =====================================================================
 * 事业合盘 · 合伙搭档（六维）
 *   ① 生肖合冲（年支）      —— 占比 10 分
 *   ② 日主生克·五合（日干） —— 占比 20 分
 *   ③ 比劫互动（合作核心）  —— 占比 25 分
 *   ④ 五行能量互补度        —— 占比 15 分
 *   ⑤ 喜用神互补度          —— 占比 20 分
 *   ⑥ 格局阴阳（纯阳/纯阴） —— 占比 10 分
 * 说明：事业合盘为传统民俗文化内容，无科学依据，评分仅供娱乐参考。
 * ===================================================================== */

/* 生肖（年支）关系的合作语境白话解析 */
function hezuoZhiText(rel, a, b) {
  switch (rel.type) {
    case "liuhe":  return `年支生肖「${a}」与「${b}」为六合，地支相合中较吉利的一类，彼此性情相投、配合默契，合作顺畅。`;
    case "sanhe":  return `年支生肖「${a}」与「${b}」为三合，彼此呼应、志趣相近，配合默契，能互相成就、共同进步。`;
    case "clash":  return `年支生肖「${a}」与「${b}」为六冲，正面相冲，性格与节奏差异较大，合作中容易起争执，需多磨合、多忍让。`;
    case "harm":   return `年支生肖「${a}」与「${b}」为相害，暗中相妨，表面平静、内里易生隔阂，需坦诚沟通、及时化解误会。`;
    case "punish": return `年支生肖「${a}」与「${b}」为相刑，长期合作易有摩擦与内耗，需彼此包容、少较真。`;
    default:       return `年支生肖「${a}」与「${b}」不冲不合，关系平和，虽无大吉大利，也没有明显冲克，顺其自然即可。`;
  }
}

/* 日主五行生克（合作语境）白话解析 */
function hezuoWuxingText(rel, zdx, ydx) {
  switch (rel.type) {
    case "sheng": return `甲方日主属${zdx}、乙方日主属${ydx}，${rel.text}，五行相生，一方能带动另一方，配合中形成良性循环，合作顺畅。`;
    case "same":  return `双方日主同属${zdx}，五行比和，思维同频、沟通成本低；但同类相叠也可能各持己见、缺乏制衡，需明确分工。`;
    case "ke":    return `甲方日主属${zdx}、乙方日主属${ydx}，${rel.text}，五行相克，合作中一方偏主导、一方易受压，需把握分寸、互相尊重。`;
    default:      return `双方日主五行平和，无明显的生克牵制，合作独立又和缓。`;
  }
}

/* 比劫互动（合作核心维度）白话解析 */
function hezuoBijieText(bjA, bjB, weakA, weakB, strongA, strongB, zdx, ydx) {
  const descA = bjA > 0.3 ? "比劫偏旺" : bjA < 0.15 ? "比劫偏弱" : "比劫适中";
  const descB = bjB > 0.3 ? "比劫偏旺" : bjB < 0.15 ? "比劫偏弱" : "比劫适中";
  let s = `甲方日主「${zdx}」${descA}（占比 ${(bjA * 100).toFixed(0)}%），乙方日主「${ydx}」${descB}（占比 ${(bjB * 100).toFixed(0)}%）。`;
  if (weakA && weakB) s += "双方身弱、皆以比劫为喜用，合作中能互为臂膀、彼此帮扶，是典型的「团队型」组合，抱团取暖、共担风雨。";
  else if (strongA && strongB) s += "双方身强、皆以比劫为忌神，合作中易因利益分配起争执、互不相让，需提前明确权责与分成。";
  else if ((weakA && strongB) || (strongA && weakB)) s += "一方身弱需帮扶、一方身强能独立，强弱互补、各司其职，适合「主内主外」式分工合作。";
  else if (weakA || weakB) s += "一方身弱需比劫帮扶、另一方身中和，合作中弱势方可得助力，整体平稳、无明显冲突。";
  else if (strongA || strongB) s += "一方身强忌比劫、另一方身中和，强势方易主导节奏，需注意分工与话语权平衡。";
  else s += "双方身中和、比劫喜忌中性，合作中既无大助力也无大冲突，属平稳型搭档，靠共同目标维系。";
  if (Math.abs(bjA - bjB) > 0.15) s += "且双方比劫强弱错位明显，能形成互补分工，减少同质竞争。";
  else if (bjA > 0.3 && bjB > 0.3) s += "但双方比劫皆旺，同质竞争强，需避免「一山二虎」、争夺主导权。";
  return s;
}

/* 天干五合（合作语境）白话解析 */
function hezuoWuheText(rel, tgA, tgB) {
  return `甲方日干「${tgA}」与乙方日干「${tgB}」为天干五合，属「有情之合」，彼此投契、配合默契，是日主层面天然合拍的象征，合作中能形成高度默契与信任。`;
}

/* 五行能量互补度（合作语境）白话解析 */
function hezuoHubuText(hubu, topA, topB) {
  let s = `甲方最旺五行为「${topA.join("、")}」，乙方最旺五行为「${topB.join("、")}」。`;
  if (hubu.identical) s += `双方五行分布完全一致、强弱趋同，亲和有余而同气过旺，缺少互补差异，合作中易思路趋同、缺乏制衡，需主动引入不同视角。`;
  else if (hubu.complement >= 2) s += `双方五行强弱明显错位、彼此补足（互补 ${hubu.complement} 项），能各取所长、互相补位，是相当理想的搭档组合。`;
  else if (hubu.complement === 1) s += `双方有 ${hubu.complement} 项五行互补，能起到一定的取长补短效果。`;
  else if (hubu.overlap >= 2) s += `双方五行缺少互补，偏强的部分重叠（${hubu.overlap} 项同类趋同），能力结构相似但易各执己见，需明确分工、互相包容。`;
  else s += `双方五行缺少互补，各自偏强的部分重叠，容易出现争夺或互相不理解。`;
  return s;
}

/* 喜用神互补度（合作语境）白话解析 */
function hezuoYongText(dimY, topA, topB) {
  const a = dimY.aFoxiangB, b = dimY.bFoxiangA;
  if (dimY.neutral) {
    const base = (a && b) ? "本来喜用互旺" : (a || b) ? "本来存在单向补益" : "本无补益";
    return `一方或双方命局为「中和」，喜用方向不明确，此维度按保守口径降档计分（${base}），避免虚高。`;
  }
  if (a && b) return `甲方最旺的「${topA[0]}」恰是乙方命局所需，乙方最旺的「${topB[0]}」也恰是甲方所需，双方喜用神互相成就，是合作中难得的「互相旺对方」组合。`;
  if (a) return `甲方最旺的「${topA[0]}」正是乙方命局所缺所需，甲能补乙，能为合作带来实质助力。`;
  if (b) return `乙方最旺的「${topB[0]}」正是甲方命局所缺所需，乙能补甲，能为合作带来实质助力。`;
  return `双方喜用神互补较弱，各自的强势之处并非对方所需，难以形成「补益」效应。`;
}

/* 事业合盘主函数：入参为双方的 execute 结果 + generate_report 结果 */
function computeHezuo(resA, repA, resB, repB) {
  const zdx = repA.me_x, ydx = repB.me_x;            // 双方日主五行
  const tgA = resA.day_tg, tgB = resB.day_tg;        // 双方日干
  const zxz = resA.year_dz, yxz = resB.year_dz;      // 双方生肖（年支）

  // —— ① 生肖（年支）满分 10 ——
  const sxRel = branchRelationHe(zxz, yxz);
  const sxScore = sxRel.type === "liuhe" ? 10 : sxRel.type === "sanhe" ? 8 : sxRel.type === "normal" ? 6 : sxRel.type === "clash" ? 0 : 3;

  // —— ② 日主（日干）：先判天干五合，再判五行生克，满分 20 ——
  let rgRel, rgScore;
  if (HE_TIANGAN_HE[tgA] === tgB) {
    rgRel = { type: "he", label: "天干相合", good: true, strong: true, text: `${tgA}${tgB}为天干五合，有情之合` };
    rgScore = 20;
  } else {
    rgRel = wuxingRelationHe(zdx, ydx);
    rgScore = rgRel.type === "sheng" ? 16 : rgRel.type === "same" ? 12 : 5;
  }

  // —— ③ 比劫互动（合作核心）满分 25 ——
  const pa = repA.elements_power, pb = repB.elements_power;
  const suma = ELEMENT_ORDER.reduce((s, w) => s + (pa[w] || 0), 0) || 1;
  const sumb = ELEMENT_ORDER.reduce((s, w) => s + (pb[w] || 0), 0) || 1;
  const bjA = (pa[zdx] || 0) / suma;                 // 甲方比劫能量占比（同我者 = 日主五行）
  const bjB = (pb[ydx] || 0) / sumb;
  const weakA = repA.strength.ratio <= 0.45, strongA = repA.strength.ratio >= 0.55;
  const weakB = repB.strength.ratio <= 0.45, strongB = repB.strength.ratio >= 0.55;
  let bjScore = 10;
  if (weakA && weakB) bjScore += 10;                 // 双方身弱需比劫 → 合作共赢
  else if (strongA && strongB) bjScore -= 4;         // 双方身强忌比劫 → 易争夺
  else if ((weakA && strongB) || (strongA && weakB)) bjScore += 5; // 强弱互补
  else if (weakA || weakB) bjScore += 3;             // 一方身弱需比劫
  else if (strongA || strongB) bjScore -= 2;         // 一方身强忌比劫
  else bjScore += 2;                                 // 双方身中和 → 喜忌中性、平稳
  const bjDiff = Math.abs(bjA - bjB);
  if (bjDiff > 0.15) bjScore += 3;                   // 比劫强弱错位 → 互补分工
  else if (bjA > 0.3 && bjB > 0.3) bjScore -= 2;     // 双方比劫皆旺 → 同质竞争
  bjScore = Math.max(0, Math.min(25, Math.round(bjScore)));

  // —— ④ 五行能量互补 满分 15 ——
  let complement = 0, overlap = 0;
  ELEMENT_ORDER.forEach(w => {
    const da = (pa[w] || 0) / suma, db = (pb[w] || 0) / sumb;
    const deva = da - 0.2, devb = db - 0.2;
    if ((deva > 0.05 && devb < -0.05) || (deva < -0.05 && devb > 0.05)) complement++;
    else if (Math.abs(deva) > 0.05 && Math.abs(devb) > 0.05 && (deva > 0) === (devb > 0)) overlap++;
  });
  let buScore = 8 + complement * 2;
  buScore = Math.max(8, Math.min(15, Math.round(buScore)));

  // —— ⑤ 喜用神互补 满分 20 ——
  const yongA = yongWuxings(zdx, repA.strength.ratio);
  const yongB = yongWuxings(ydx, repB.strength.ratio);
  const topB = topWuxings(pb), topA = topWuxings(pa);
  const aFoxiangB = yongB.some(w => topA[0] === w);
  const bFoxiangA = yongA.some(w => topB[0] === w);
  const aErxiangB = yongB.some(w => topA[1] === w);
  const bErxiangA = yongA.some(w => topB[1] === w);
  let yongScore;
  if (aFoxiangB && bFoxiangA) yongScore = 20;
  else if (aFoxiangB || bFoxiangA || (aErxiangB && bErxiangA)) yongScore = 14;
  else if (aErxiangB || bErxiangA) yongScore = 10;
  else yongScore = 6;
  const neutralA = repA.strength.ratio > 0.45 && repA.strength.ratio < 0.55;
  const neutralB = repB.strength.ratio > 0.45 && repB.strength.ratio < 0.55;
  const neutral = neutralA || neutralB;
  if (neutral) {
    if (yongScore === 20) yongScore = 14;
    else if (yongScore === 14) yongScore = 10;
    else if (yongScore === 10) yongScore = 8;
  }

  // —— ⑥ 格局阴阳 满分 10 ——
  const pureA = detectPureYinYang(resA), pureB = detectPureYinYang(resB);
  const aPure = pureA !== "非纯", bPure = pureB !== "非纯";
  let gejuScore, gejuText;
  if (aPure && bPure && pureA !== pureB) {
    gejuScore = 10;
    gejuText = `甲方为「${pureA}」、乙方为「${pureB}」，孤阳遇孤阴、刚柔相济，阴阳得以调合，属难得的互补格局。`;
  } else if (pureA === "纯阳" && pureB === "纯阳") {
    gejuScore = 3;
    gejuText = "双方均为纯阳之命，阳气过盛、性格皆偏刚烈强势，合作中易硬碰硬、争夺主导，需以柔克刚、明确分工。";
  } else if (pureA === "纯阴" && pureB === "纯阴") {
    gejuScore = 3;
    gejuText = "双方均为纯阴之命，阴气偏重、性格皆内敛敏感，合作中易冷处理、生隔阂，需主动沟通、坦诚交心。";
  } else if (aPure || bPure) {
    gejuScore = 6;
    const pureSide = aPure ? "甲方" : "乙方";
    const pureKind = aPure ? pureA : pureB;
    gejuText = `${pureSide}为「${pureKind}」独特性格格局、另一方为常规格局；纯者偏执一端，需对方以包容调剂，互补中略带磨合。`;
  } else {
    gejuScore = 5;
    gejuText = "双方均为常规格局（非纯阳、非纯阴），阴阳分布平稳，无特殊偏枯之象。";
  }

  const score = sxScore + rgScore + bjScore + buScore + yongScore + gejuScore;
  let level, verdict;
  if (score >= 85) { level = "上等搭档"; verdict = "互补点突出：生肖、日主与比劫互动高度契合，五行互补，能各展所长、互相成就。建议明确分工、各守其位，把默契转化为稳定产出。"; }
  else if (score >= 70) { level = "良好搭档"; verdict = "互补点：契合度较高，分工明确、配合默契。摩擦点：需留意权责边界。建议提前约定规则、保持信息同步，即可高效协作。"; }
  else if (score >= 55) { level = "一般搭档"; verdict = "互补点：有一定配合基础。摩擦点：性格与节奏差异需磨合。建议多沟通、把差异化为互补优势，避免各执己见。"; }
  else if (score >= 40) { level = "磨合搭档"; verdict = "摩擦点：契合度偏低，易有摩擦与利益分歧。建议务必提前约定权责与利益分配，保持耐心、降低预期。"; }
  else { level = "冲突风险较高"; verdict = "摩擦点：冲克较重，合作易生冲突与内耗。建议若非必要不建议深度绑定；如必须合作，需书面约定规则并保持距离感。"; }

  // 四柱完全相同：专门文案，避免被通用档位"冲克"措辞误导
  const identical = resA.year_tg  === resB.year_tg  && resA.year_dz  === resB.year_dz &&
                    resA.month_tg === resB.month_tg && resA.month_dz === resB.month_dz &&
                    resA.day_tg   === resB.day_tg   && resA.day_dz   === resB.day_dz &&
                    resA.hour_tg  === resB.hour_tg  && resA.hour_dz  === resB.hour_dz;
  if (identical) {
    level = "同频搭档";
    verdict = "双方八字如出一辙，思维方式与行事节奏高度同频，默契十足、沟通成本低。摩擦点：同气过旺而五行缺互补，易趋同固执、缺乏制衡。建议：明确分工、避免各自为政，主动引入不同视角。";
  }

  // —— 详细白话解析 ——
  const analysis = {
    summary: `甲方日主「${resA.ri_zhu}」属${zdx}、生肖${ZODIAC[zxz]}（${zxz}），乙方日主「${resB.ri_zhu}」属${ydx}、生肖${ZODIAC[yxz]}（${yxz}），六维综合 ${score} 分，属「${level}」。${verdict}`,
    shengxiao: hezuoZhiText(sxRel, zxz, yxz),
    rigan:    rgRel.type === "he" ? hezuoWuheText(rgRel, tgA, tgB) : hezuoWuxingText(rgRel, zdx, ydx),
    bijie:    hezuoBijieText(bjA, bjB, weakA, weakB, strongA, strongB, zdx, ydx),
    hubu:     hezuoHubuText({ complement, overlap, identical }, topA, topB),
    yongshen: hezuoYongText({ aFoxiangB, bFoxiangA, neutral }, topA, topB),
    geju:     gejuText
  };

  return {
    score, level, verdict, analysis,
    a: { ri_zhu: resA.ri_zhu, me_x: zdx, year_zhi: zxz, day_zhi: resA.day_dz, power: pa, top: topA, yong: yongA, pure: pureA, bijie: bjA },
    b: { ri_zhu: resB.ri_zhu, me_x: ydx, year_zhi: yxz, day_zhi: resB.day_dz, power: pb, top: topB, yong: yongB, pure: pureB, bijie: bjB },
    dims: {
      shengxiao: { score: sxScore, rel: sxRel },
      rigan:    { score: rgScore, rel: rgRel },
      bijie:    { score: bjScore, bjA, bjB, weakA, weakB, strongA, strongB },
      hubu:     { score: buScore, complement, overlap },
      yongshen: { score: yongScore, aFoxiangB, bFoxiangA, neutral },
      geju:     { score: gejuScore, pureA, pureB }
    }
  };
}

/* ---------------- 导出（浏览器 / Node 双端） ---------------- */
if (typeof module !== "undefined" && module.exports) {
  module.exports = {
    TIANGAN, DIZHI, WU_XING, YIN_YANG, SHISHEN_MAP, PROVINCE_FALLBACK_LNG,
    HIDDEN_STEMS, TERM_NAMES,
    is_valid_date, date_to_julian_day, get_shishen_relation, primaryHiddenStem,
    solarTermUtJd, equationOfTime, localToUtcMs, getTimeZoneOffsetMs, getStandardOffsetMin,
    computeDayunAndLiuNian, liunianGanzhi, jdToDate,
    computeMarriageAndCareer, isYongShen, computeHehun, detectPureYinYang, hehunWuheText,
    computeHezuo, hezuoZhiText, hezuoWuxingText, hezuoBijieText, hezuoWuheText, hezuoHubuText, hezuoYongText,
    execute_global_fortune_engine, generate_report, PATTERN_DETAILS, FALLBACK_DETAIL,
    SHISHEN_DETAILS, PILLAR_MEANING, TIANGAN_CHARACTER, SHISHEN_GROUP, elementShishenGroup
  };
} else {
  window.BaziEngine = {
    TIANGAN, DIZHI, WU_XING, YIN_YANG, SHISHEN_MAP, PROVINCE_FALLBACK_LNG,
    HIDDEN_STEMS, TERM_NAMES,
    is_valid_date, date_to_julian_day, get_shishen_relation, primaryHiddenStem,
    solarTermUtJd, equationOfTime, localToUtcMs, getTimeZoneOffsetMs, getStandardOffsetMin,
    computeDayunAndLiuNian, liunianGanzhi, jdToDate,
    computeMarriageAndCareer, isYongShen, computeHehun, detectPureYinYang, hehunWuheText,
    computeHezuo, hezuoZhiText, hezuoWuxingText, hezuoBijieText, hezuoWuheText, hezuoHubuText, hezuoYongText,
    execute_global_fortune_engine, generate_report, PATTERN_DETAILS, FALLBACK_DETAIL,
    SHISHEN_DETAILS, PILLAR_MEANING, TIANGAN_CHARACTER, SHISHEN_GROUP, elementShishenGroup
  };
}